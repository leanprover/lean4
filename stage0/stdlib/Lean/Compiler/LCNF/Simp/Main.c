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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* x_165; 
x_165 = lean_box(0);
x_12 = x_165;
x_13 = x_9;
goto block_164;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_12 = x_166;
x_13 = x_9;
goto block_164;
}
block_164:
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_hasLocalInst(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_160; 
x_160 = lean_box(0);
x_32 = x_160;
x_33 = x_23;
goto block_159;
}
else
{
lean_object* x_161; 
x_161 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_32 = x_161;
x_33 = x_23;
goto block_159;
}
block_159:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_34 = lean_box(0);
if (lean_is_scalar(x_24)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_24;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_156; 
lean_dec(x_32);
lean_dec(x_24);
lean_inc(x_17);
x_36 = l_Lean_Meta_isInstance(x_17, x_7, x_8, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_156 = lean_unbox(x_37);
lean_dec(x_37);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = 1;
x_40 = x_157;
goto block_155;
}
else
{
uint8_t x_158; 
x_158 = 0;
x_40 = x_158;
goto block_155;
}
block_155:
{
lean_object* x_41; lean_object* x_42; 
if (x_40 == 0)
{
lean_object* x_153; 
x_153 = lean_box(0);
x_41 = x_153;
x_42 = x_38;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_41 = x_154;
x_42 = x_38;
goto block_152;
}
block_152:
{
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_39;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_41);
lean_dec(x_39);
lean_inc(x_17);
x_45 = l_Lean_Compiler_LCNF_getDecl_x3f(x_17, x_5, x_6, x_7, x_8, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
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
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
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
x_56 = lean_array_get_size(x_19);
x_57 = l_Lean_Compiler_LCNF_Decl_getArity(x_55);
lean_dec(x_55);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_150; 
x_150 = lean_box(0);
x_59 = x_150;
x_60 = x_53;
goto block_149;
}
else
{
lean_object* x_151; 
x_151 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_59 = x_151;
x_60 = x_53;
goto block_149;
}
block_149:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_61 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_54;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_dec(x_54);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; size_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_64 = lean_ctor_get(x_59, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_1, 2);
lean_inc(x_65);
x_66 = l_Lean_Compiler_LCNF_mkNewParams(x_65, x_5, x_6, x_7, x_8, x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_array_get_size(x_67);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = 0;
lean_inc(x_67);
x_72 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_70, x_71, x_67);
x_73 = l_Array_append___rarg(x_19, x_72);
if (lean_is_scalar(x_20)) {
 x_74 = lean_alloc_ctor(3, 3, 0);
} else {
 x_74 = x_20;
}
lean_ctor_set(x_74, 0, x_17);
lean_ctor_set(x_74, 1, x_18);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_74, x_75, x_5, x_6, x_7, x_8, x_68);
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
x_83 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_67, x_81, x_82, x_5, x_6, x_7, x_8, x_78);
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
lean_ctor_set(x_59, 0, x_84);
lean_ctor_set(x_90, 0, x_59);
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
lean_ctor_set(x_59, 0, x_84);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_59);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_84);
lean_free_object(x_59);
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
lean_free_object(x_59);
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
lean_dec(x_67);
lean_free_object(x_59);
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
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_59);
x_107 = lean_ctor_get(x_1, 2);
lean_inc(x_107);
x_108 = l_Lean_Compiler_LCNF_mkNewParams(x_107, x_5, x_6, x_7, x_8, x_60);
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
x_114 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_112, x_113, x_109);
x_115 = l_Array_append___rarg(x_19, x_114);
if (lean_is_scalar(x_20)) {
 x_116 = lean_alloc_ctor(3, 3, 0);
} else {
 x_116 = x_20;
}
lean_ctor_set(x_116, 0, x_17);
lean_ctor_set(x_116, 1, x_18);
lean_ctor_set(x_116, 2, x_115);
x_117 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_116, x_117, x_5, x_6, x_7, x_8, x_110);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_125 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_109, x_123, x_124, x_5, x_6, x_7, x_8, x_120);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_1, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_128, x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_131);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_ctor_set(x_135, 0, x_126);
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
lean_dec(x_126);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_137 = lean_ctor_get(x_130, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_139 = x_130;
} else {
 lean_dec_ref(x_130);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_141 = lean_ctor_get(x_125, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_143 = x_125;
} else {
 lean_dec_ref(x_125);
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
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_145 = lean_ctor_get(x_118, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_118, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_147 = x_118;
} else {
 lean_dec_ref(x_118);
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
lean_object* x_162; lean_object* x_163; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_162 = lean_box(0);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_13);
return x_163;
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
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_230; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_230 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_230 == 0)
{
x_38 = x_34;
goto block_229;
}
else
{
uint8_t x_231; 
x_231 = lean_nat_dec_eq(x_24, x_27);
x_38 = x_231;
goto block_229;
}
block_229:
{
if (x_38 == 0)
{
lean_object* x_39; 
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
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_215 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 0);
if (lean_is_scalar(x_22)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_22;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_217, 0, x_220);
return x_217;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_217, 0);
x_222 = lean_ctor_get(x_217, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_217);
if (lean_is_scalar(x_22)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_22;
}
lean_ctor_set(x_223, 0, x_221);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
else
{
uint8_t x_225; 
lean_dec(x_22);
x_225 = !lean_is_exclusive(x_217);
if (x_225 == 0)
{
return x_217;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_217, 0);
x_227 = lean_ctor_get(x_217, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_217);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
}
}
else
{
uint8_t x_232; 
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
x_232 = !lean_is_exclusive(x_35);
if (x_232 == 0)
{
return x_35;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_35, 0);
x_234 = lean_ctor_get(x_35, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_35);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
case 1:
{
uint8_t x_236; lean_object* x_237; 
x_236 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_237 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_236, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_432; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_432 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_432 == 0)
{
x_240 = x_236;
goto block_431;
}
else
{
uint8_t x_433; 
x_433 = lean_nat_dec_eq(x_24, x_27);
x_240 = x_433;
goto block_431;
}
block_431:
{
if (x_240 == 0)
{
lean_object* x_241; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_241 = l_Lean_Compiler_LCNF_Simp_simp(x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
lean_inc(x_242);
x_244 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_242);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_245 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_243);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_ctor_get(x_21, 2);
lean_inc(x_247);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_248 = l_Lean_Compiler_LCNF_inferAppType(x_247, x_33, x_6, x_7, x_8, x_9, x_246);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_249);
x_251 = l_Lean_Expr_headBeta(x_249);
x_252 = l_Lean_Expr_isForall(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; 
x_253 = l_Lean_Compiler_LCNF_mkAuxParam(x_249, x_236, x_6, x_7, x_8, x_9, x_250);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_ctor_get(x_254, 0);
lean_inc(x_256);
x_257 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_257 == 0)
{
lean_object* x_286; 
lean_dec(x_27);
lean_dec(x_23);
x_286 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_256, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_255);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_288 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_258 = x_289;
x_259 = x_290;
goto block_285;
}
else
{
uint8_t x_291; 
lean_dec(x_254);
lean_dec(x_242);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_291 = !lean_is_exclusive(x_288);
if (x_291 == 0)
{
return x_288;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_288, 0);
x_293 = lean_ctor_get(x_288, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_288);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_254);
lean_dec(x_242);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = !lean_is_exclusive(x_286);
if (x_295 == 0)
{
return x_286;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_286, 0);
x_297 = lean_ctor_get(x_286, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_286);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_299 = lean_array_get_size(x_23);
x_300 = l_Array_toSubarray___rarg(x_23, x_27, x_299);
x_301 = l_Array_ofSubarray___rarg(x_300);
x_302 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_302, 0, x_256);
lean_ctor_set(x_302, 1, x_301);
x_303 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_304 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_302, x_303, x_6, x_7, x_8, x_9, x_255);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_305, 0);
lean_inc(x_307);
x_308 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_307, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_306);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_305);
lean_ctor_set(x_310, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_311 = l_Lean_Compiler_LCNF_Simp_simp(x_310, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_309);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_258 = x_312;
x_259 = x_313;
goto block_285;
}
else
{
uint8_t x_314; 
lean_dec(x_254);
lean_dec(x_242);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_314 = !lean_is_exclusive(x_311);
if (x_314 == 0)
{
return x_311;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_311, 0);
x_316 = lean_ctor_get(x_311, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_311);
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
lean_dec(x_305);
lean_dec(x_254);
lean_dec(x_242);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_318 = !lean_is_exclusive(x_308);
if (x_318 == 0)
{
return x_308;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_308, 0);
x_320 = lean_ctor_get(x_308, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_308);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
return x_321;
}
}
}
else
{
uint8_t x_322; 
lean_dec(x_254);
lean_dec(x_242);
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
x_322 = !lean_is_exclusive(x_304);
if (x_322 == 0)
{
return x_304;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_304, 0);
x_324 = lean_ctor_get(x_304, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_304);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
block_285:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_261 = lean_array_push(x_260, x_254);
x_262 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_263 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_261, x_258, x_262, x_6, x_7, x_8, x_9, x_259);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_264);
x_266 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_266, 0, x_264);
lean_closure_set(x_266, 1, x_260);
x_267 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_242, x_266, x_6, x_7, x_8, x_9, x_265);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_270, 0, x_264);
lean_ctor_set(x_270, 1, x_269);
if (lean_is_scalar(x_22)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_22;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_267, 0, x_271);
return x_267;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_ctor_get(x_267, 0);
x_273 = lean_ctor_get(x_267, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_267);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_264);
lean_ctor_set(x_274, 1, x_272);
if (lean_is_scalar(x_22)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_22;
}
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_273);
return x_276;
}
}
else
{
uint8_t x_277; 
lean_dec(x_264);
lean_dec(x_22);
x_277 = !lean_is_exclusive(x_267);
if (x_277 == 0)
{
return x_267;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_267, 0);
x_279 = lean_ctor_get(x_267, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_267);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_242);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_281 = !lean_is_exclusive(x_263);
if (x_281 == 0)
{
return x_263;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_263, 0);
x_283 = lean_ctor_get(x_263, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_263);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_249);
x_326 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_327 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_328 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_326, x_242, x_327, x_6, x_7, x_8, x_9, x_250);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_331 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_329, x_6, x_7, x_8, x_9, x_330);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
x_335 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_335 == 0)
{
lean_object* x_350; 
lean_dec(x_27);
lean_dec(x_23);
x_350 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_334, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_333);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_352 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 1);
lean_inc(x_354);
lean_dec(x_352);
x_336 = x_353;
x_337 = x_354;
goto block_349;
}
else
{
uint8_t x_355; 
lean_dec(x_332);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_355 = !lean_is_exclusive(x_352);
if (x_355 == 0)
{
return x_352;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 0);
x_357 = lean_ctor_get(x_352, 1);
lean_inc(x_357);
lean_inc(x_356);
lean_dec(x_352);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_332);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = !lean_is_exclusive(x_350);
if (x_359 == 0)
{
return x_350;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_350, 0);
x_361 = lean_ctor_get(x_350, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_350);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_array_get_size(x_23);
x_364 = l_Array_toSubarray___rarg(x_23, x_27, x_363);
x_365 = l_Array_ofSubarray___rarg(x_364);
x_366 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_366, 0, x_334);
lean_ctor_set(x_366, 1, x_365);
x_367 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_368 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_366, x_367, x_6, x_7, x_8, x_9, x_333);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
x_372 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_371, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_370);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_369);
lean_ctor_set(x_374, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_375 = l_Lean_Compiler_LCNF_Simp_simp(x_374, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_373);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
lean_dec(x_375);
x_336 = x_376;
x_337 = x_377;
goto block_349;
}
else
{
uint8_t x_378; 
lean_dec(x_332);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_378 = !lean_is_exclusive(x_375);
if (x_378 == 0)
{
return x_375;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_375, 0);
x_380 = lean_ctor_get(x_375, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_375);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_369);
lean_dec(x_332);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_372);
if (x_382 == 0)
{
return x_372;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_372, 0);
x_384 = lean_ctor_get(x_372, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_372);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_332);
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
x_386 = !lean_is_exclusive(x_368);
if (x_386 == 0)
{
return x_368;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_368, 0);
x_388 = lean_ctor_get(x_368, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_368);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
block_349:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_338, 0, x_332);
x_339 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_340 = lean_array_push(x_339, x_338);
x_341 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_340, x_336, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_337);
lean_dec(x_340);
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
x_343 = lean_ctor_get(x_341, 0);
if (lean_is_scalar(x_22)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_22;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_341, 0, x_344);
return x_341;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_341, 0);
x_346 = lean_ctor_get(x_341, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_341);
if (lean_is_scalar(x_22)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_22;
}
lean_ctor_set(x_347, 0, x_345);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
}
else
{
uint8_t x_390; 
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
x_390 = !lean_is_exclusive(x_331);
if (x_390 == 0)
{
return x_331;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_331, 0);
x_392 = lean_ctor_get(x_331, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_331);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
else
{
uint8_t x_394; 
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
x_394 = !lean_is_exclusive(x_328);
if (x_394 == 0)
{
return x_328;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_328, 0);
x_396 = lean_ctor_get(x_328, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_328);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_33);
lean_dec(x_21);
x_398 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_243);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_400, 0, x_3);
lean_closure_set(x_400, 1, x_4);
lean_closure_set(x_400, 2, x_5);
lean_closure_set(x_400, 3, x_27);
lean_closure_set(x_400, 4, x_24);
lean_closure_set(x_400, 5, x_26);
lean_closure_set(x_400, 6, x_2);
lean_closure_set(x_400, 7, x_23);
x_401 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_242, x_400, x_6, x_7, x_8, x_9, x_399);
if (lean_obj_tag(x_401) == 0)
{
uint8_t x_402; 
x_402 = !lean_is_exclusive(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
x_403 = lean_ctor_get(x_401, 0);
if (lean_is_scalar(x_22)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_22;
}
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_401, 0, x_404);
return x_401;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_405 = lean_ctor_get(x_401, 0);
x_406 = lean_ctor_get(x_401, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_401);
if (lean_is_scalar(x_22)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_22;
}
lean_ctor_set(x_407, 0, x_405);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
else
{
uint8_t x_409; 
lean_dec(x_22);
x_409 = !lean_is_exclusive(x_401);
if (x_409 == 0)
{
return x_401;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_401, 0);
x_411 = lean_ctor_get(x_401, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_401);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
}
else
{
uint8_t x_413; 
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
x_413 = !lean_is_exclusive(x_241);
if (x_413 == 0)
{
return x_241;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_241, 0);
x_415 = lean_ctor_get(x_241, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_241);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_417 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_239);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
x_419 = l_Lean_Compiler_LCNF_Simp_simp(x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_418);
if (lean_obj_tag(x_419) == 0)
{
uint8_t x_420; 
x_420 = !lean_is_exclusive(x_419);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_419, 0);
if (lean_is_scalar(x_22)) {
 x_422 = lean_alloc_ctor(1, 1, 0);
} else {
 x_422 = x_22;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_419, 0, x_422);
return x_419;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_419, 0);
x_424 = lean_ctor_get(x_419, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_419);
if (lean_is_scalar(x_22)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_22;
}
lean_ctor_set(x_425, 0, x_423);
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
uint8_t x_427; 
lean_dec(x_22);
x_427 = !lean_is_exclusive(x_419);
if (x_427 == 0)
{
return x_419;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_ctor_get(x_419, 0);
x_429 = lean_ctor_get(x_419, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_419);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_429);
return x_430;
}
}
}
}
}
else
{
uint8_t x_434; 
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
x_434 = !lean_is_exclusive(x_237);
if (x_434 == 0)
{
return x_237;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_237, 0);
x_436 = lean_ctor_get(x_237, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_237);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
case 2:
{
uint8_t x_438; lean_object* x_439; 
lean_dec(x_11);
x_438 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_439 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_438, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; uint8_t x_634; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_634 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_634 == 0)
{
x_442 = x_438;
goto block_633;
}
else
{
uint8_t x_635; 
x_635 = lean_nat_dec_eq(x_24, x_27);
x_442 = x_635;
goto block_633;
}
block_633:
{
if (x_442 == 0)
{
lean_object* x_443; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_443 = l_Lean_Compiler_LCNF_Simp_simp(x_440, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_441);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
lean_inc(x_444);
x_446 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_444);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
x_447 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_445);
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
lean_dec(x_447);
x_449 = lean_ctor_get(x_21, 2);
lean_inc(x_449);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_450 = l_Lean_Compiler_LCNF_inferAppType(x_449, x_33, x_6, x_7, x_8, x_9, x_448);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
lean_inc(x_451);
x_453 = l_Lean_Expr_headBeta(x_451);
x_454 = l_Lean_Expr_isForall(x_453);
lean_dec(x_453);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; 
x_455 = l_Lean_Compiler_LCNF_mkAuxParam(x_451, x_438, x_6, x_7, x_8, x_9, x_452);
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_ctor_get(x_456, 0);
lean_inc(x_458);
x_459 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_459 == 0)
{
lean_object* x_488; 
lean_dec(x_27);
lean_dec(x_23);
x_488 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_458, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_457);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_490 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_460 = x_491;
x_461 = x_492;
goto block_487;
}
else
{
uint8_t x_493; 
lean_dec(x_456);
lean_dec(x_444);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_493 = !lean_is_exclusive(x_490);
if (x_493 == 0)
{
return x_490;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_490, 0);
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_490);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
else
{
uint8_t x_497; 
lean_dec(x_456);
lean_dec(x_444);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_497 = !lean_is_exclusive(x_488);
if (x_497 == 0)
{
return x_488;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_488, 0);
x_499 = lean_ctor_get(x_488, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_488);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_501 = lean_array_get_size(x_23);
x_502 = l_Array_toSubarray___rarg(x_23, x_27, x_501);
x_503 = l_Array_ofSubarray___rarg(x_502);
x_504 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_504, 0, x_458);
lean_ctor_set(x_504, 1, x_503);
x_505 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_506 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_504, x_505, x_6, x_7, x_8, x_9, x_457);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
x_510 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_509, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_508);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
lean_dec(x_510);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_507);
lean_ctor_set(x_512, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_513 = l_Lean_Compiler_LCNF_Simp_simp(x_512, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_511);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_460 = x_514;
x_461 = x_515;
goto block_487;
}
else
{
uint8_t x_516; 
lean_dec(x_456);
lean_dec(x_444);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_516 = !lean_is_exclusive(x_513);
if (x_516 == 0)
{
return x_513;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_513, 0);
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_513);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
uint8_t x_520; 
lean_dec(x_507);
lean_dec(x_456);
lean_dec(x_444);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_520 = !lean_is_exclusive(x_510);
if (x_520 == 0)
{
return x_510;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_510, 0);
x_522 = lean_ctor_get(x_510, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_510);
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
lean_dec(x_456);
lean_dec(x_444);
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
x_524 = !lean_is_exclusive(x_506);
if (x_524 == 0)
{
return x_506;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_506, 0);
x_526 = lean_ctor_get(x_506, 1);
lean_inc(x_526);
lean_inc(x_525);
lean_dec(x_506);
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
return x_527;
}
}
}
block_487:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_462 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_463 = lean_array_push(x_462, x_456);
x_464 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_465 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_463, x_460, x_464, x_6, x_7, x_8, x_9, x_461);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_466);
x_468 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_468, 0, x_466);
lean_closure_set(x_468, 1, x_462);
x_469 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_444, x_468, x_6, x_7, x_8, x_9, x_467);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_472, 0, x_466);
lean_ctor_set(x_472, 1, x_471);
if (lean_is_scalar(x_22)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_22;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_469, 0, x_473);
return x_469;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_474 = lean_ctor_get(x_469, 0);
x_475 = lean_ctor_get(x_469, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_469);
x_476 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_476, 0, x_466);
lean_ctor_set(x_476, 1, x_474);
if (lean_is_scalar(x_22)) {
 x_477 = lean_alloc_ctor(1, 1, 0);
} else {
 x_477 = x_22;
}
lean_ctor_set(x_477, 0, x_476);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_475);
return x_478;
}
}
else
{
uint8_t x_479; 
lean_dec(x_466);
lean_dec(x_22);
x_479 = !lean_is_exclusive(x_469);
if (x_479 == 0)
{
return x_469;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_469, 0);
x_481 = lean_ctor_get(x_469, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_469);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_444);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_483 = !lean_is_exclusive(x_465);
if (x_483 == 0)
{
return x_465;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_465, 0);
x_485 = lean_ctor_get(x_465, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_465);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_451);
x_528 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_529 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_530 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_528, x_444, x_529, x_6, x_7, x_8, x_9, x_452);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_533 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_531, x_6, x_7, x_8, x_9, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; lean_object* x_539; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = lean_ctor_get(x_534, 0);
lean_inc(x_536);
x_537 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_537 == 0)
{
lean_object* x_552; 
lean_dec(x_27);
lean_dec(x_23);
x_552 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_536, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_535);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_554 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_553);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_538 = x_555;
x_539 = x_556;
goto block_551;
}
else
{
uint8_t x_557; 
lean_dec(x_534);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_557 = !lean_is_exclusive(x_554);
if (x_557 == 0)
{
return x_554;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_554, 0);
x_559 = lean_ctor_get(x_554, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_554);
x_560 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
else
{
uint8_t x_561; 
lean_dec(x_534);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_561 = !lean_is_exclusive(x_552);
if (x_561 == 0)
{
return x_552;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_552, 0);
x_563 = lean_ctor_get(x_552, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_552);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_565 = lean_array_get_size(x_23);
x_566 = l_Array_toSubarray___rarg(x_23, x_27, x_565);
x_567 = l_Array_ofSubarray___rarg(x_566);
x_568 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_568, 0, x_536);
lean_ctor_set(x_568, 1, x_567);
x_569 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_570 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_568, x_569, x_6, x_7, x_8, x_9, x_535);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
x_573 = lean_ctor_get(x_571, 0);
lean_inc(x_573);
x_574 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_573, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_572);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
lean_dec(x_574);
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_571);
lean_ctor_set(x_576, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_577 = l_Lean_Compiler_LCNF_Simp_simp(x_576, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_575);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_538 = x_578;
x_539 = x_579;
goto block_551;
}
else
{
uint8_t x_580; 
lean_dec(x_534);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_580 = !lean_is_exclusive(x_577);
if (x_580 == 0)
{
return x_577;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_577, 0);
x_582 = lean_ctor_get(x_577, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_577);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_571);
lean_dec(x_534);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_584 = !lean_is_exclusive(x_574);
if (x_584 == 0)
{
return x_574;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_574, 0);
x_586 = lean_ctor_get(x_574, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_574);
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
lean_dec(x_534);
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
x_588 = !lean_is_exclusive(x_570);
if (x_588 == 0)
{
return x_570;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_570, 0);
x_590 = lean_ctor_get(x_570, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_570);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
block_551:
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_534);
x_541 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_542 = lean_array_push(x_541, x_540);
x_543 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_542, x_538, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_539);
lean_dec(x_542);
x_544 = !lean_is_exclusive(x_543);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_543, 0);
if (lean_is_scalar(x_22)) {
 x_546 = lean_alloc_ctor(1, 1, 0);
} else {
 x_546 = x_22;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_543, 0, x_546);
return x_543;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_547 = lean_ctor_get(x_543, 0);
x_548 = lean_ctor_get(x_543, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_543);
if (lean_is_scalar(x_22)) {
 x_549 = lean_alloc_ctor(1, 1, 0);
} else {
 x_549 = x_22;
}
lean_ctor_set(x_549, 0, x_547);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
}
else
{
uint8_t x_592; 
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
x_592 = !lean_is_exclusive(x_533);
if (x_592 == 0)
{
return x_533;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_533, 0);
x_594 = lean_ctor_get(x_533, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_533);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
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
x_596 = !lean_is_exclusive(x_530);
if (x_596 == 0)
{
return x_530;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_530, 0);
x_598 = lean_ctor_get(x_530, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_530);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_33);
lean_dec(x_21);
x_600 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_445);
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
lean_dec(x_600);
x_602 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_602, 0, x_3);
lean_closure_set(x_602, 1, x_4);
lean_closure_set(x_602, 2, x_5);
lean_closure_set(x_602, 3, x_27);
lean_closure_set(x_602, 4, x_24);
lean_closure_set(x_602, 5, x_26);
lean_closure_set(x_602, 6, x_2);
lean_closure_set(x_602, 7, x_23);
x_603 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_444, x_602, x_6, x_7, x_8, x_9, x_601);
if (lean_obj_tag(x_603) == 0)
{
uint8_t x_604; 
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_603, 0);
if (lean_is_scalar(x_22)) {
 x_606 = lean_alloc_ctor(1, 1, 0);
} else {
 x_606 = x_22;
}
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_603, 0, x_606);
return x_603;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_603, 0);
x_608 = lean_ctor_get(x_603, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_603);
if (lean_is_scalar(x_22)) {
 x_609 = lean_alloc_ctor(1, 1, 0);
} else {
 x_609 = x_22;
}
lean_ctor_set(x_609, 0, x_607);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
return x_610;
}
}
else
{
uint8_t x_611; 
lean_dec(x_22);
x_611 = !lean_is_exclusive(x_603);
if (x_611 == 0)
{
return x_603;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = lean_ctor_get(x_603, 0);
x_613 = lean_ctor_get(x_603, 1);
lean_inc(x_613);
lean_inc(x_612);
lean_dec(x_603);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_612);
lean_ctor_set(x_614, 1, x_613);
return x_614;
}
}
}
}
else
{
uint8_t x_615; 
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
x_615 = !lean_is_exclusive(x_443);
if (x_615 == 0)
{
return x_443;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_443, 0);
x_617 = lean_ctor_get(x_443, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_443);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_619 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_441);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
x_621 = l_Lean_Compiler_LCNF_Simp_simp(x_440, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_620);
if (lean_obj_tag(x_621) == 0)
{
uint8_t x_622; 
x_622 = !lean_is_exclusive(x_621);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; 
x_623 = lean_ctor_get(x_621, 0);
if (lean_is_scalar(x_22)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_22;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_621, 0, x_624);
return x_621;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_625 = lean_ctor_get(x_621, 0);
x_626 = lean_ctor_get(x_621, 1);
lean_inc(x_626);
lean_inc(x_625);
lean_dec(x_621);
if (lean_is_scalar(x_22)) {
 x_627 = lean_alloc_ctor(1, 1, 0);
} else {
 x_627 = x_22;
}
lean_ctor_set(x_627, 0, x_625);
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
uint8_t x_629; 
lean_dec(x_22);
x_629 = !lean_is_exclusive(x_621);
if (x_629 == 0)
{
return x_621;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_621, 0);
x_631 = lean_ctor_get(x_621, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_621);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
}
}
}
else
{
uint8_t x_636; 
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
x_636 = !lean_is_exclusive(x_439);
if (x_636 == 0)
{
return x_439;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_439, 0);
x_638 = lean_ctor_get(x_439, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_439);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
case 3:
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_11, 0);
lean_inc(x_640);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_640);
x_641 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_640, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = !lean_is_exclusive(x_3);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; 
x_645 = lean_ctor_get(x_3, 2);
x_646 = lean_ctor_get(x_3, 3);
lean_inc(x_640);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_640);
lean_ctor_set(x_647, 1, x_645);
x_648 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_646, x_640, x_642);
lean_ctor_set(x_3, 3, x_648);
lean_ctor_set(x_3, 2, x_647);
x_649 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_650 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_649, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_643);
lean_dec(x_29);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; uint8_t x_653; uint8_t x_845; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
lean_dec(x_650);
x_845 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_845 == 0)
{
x_653 = x_649;
goto block_844;
}
else
{
uint8_t x_846; 
x_846 = lean_nat_dec_eq(x_24, x_27);
x_653 = x_846;
goto block_844;
}
block_844:
{
if (x_653 == 0)
{
lean_object* x_654; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_654 = l_Lean_Compiler_LCNF_Simp_simp(x_651, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_652);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; uint8_t x_657; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
lean_inc(x_655);
x_657 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_655);
if (x_657 == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_658 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_656);
x_659 = lean_ctor_get(x_658, 1);
lean_inc(x_659);
lean_dec(x_658);
x_660 = lean_ctor_get(x_21, 2);
lean_inc(x_660);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_661 = l_Lean_Compiler_LCNF_inferAppType(x_660, x_33, x_6, x_7, x_8, x_9, x_659);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
lean_inc(x_662);
x_664 = l_Lean_Expr_headBeta(x_662);
x_665 = l_Lean_Expr_isForall(x_664);
lean_dec(x_664);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; uint8_t x_670; lean_object* x_671; lean_object* x_672; 
x_666 = l_Lean_Compiler_LCNF_mkAuxParam(x_662, x_649, x_6, x_7, x_8, x_9, x_663);
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
x_669 = lean_ctor_get(x_667, 0);
lean_inc(x_669);
x_670 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_670 == 0)
{
lean_object* x_699; 
lean_dec(x_27);
lean_dec(x_23);
x_699 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_669, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_668);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; 
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_701 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_700);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
x_671 = x_702;
x_672 = x_703;
goto block_698;
}
else
{
uint8_t x_704; 
lean_dec(x_667);
lean_dec(x_655);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_704 = !lean_is_exclusive(x_701);
if (x_704 == 0)
{
return x_701;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_701, 0);
x_706 = lean_ctor_get(x_701, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_701);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_667);
lean_dec(x_655);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_708 = !lean_is_exclusive(x_699);
if (x_708 == 0)
{
return x_699;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_699, 0);
x_710 = lean_ctor_get(x_699, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_699);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
else
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_712 = lean_array_get_size(x_23);
x_713 = l_Array_toSubarray___rarg(x_23, x_27, x_712);
x_714 = l_Array_ofSubarray___rarg(x_713);
x_715 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_715, 0, x_669);
lean_ctor_set(x_715, 1, x_714);
x_716 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_717 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_715, x_716, x_6, x_7, x_8, x_9, x_668);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
x_720 = lean_ctor_get(x_718, 0);
lean_inc(x_720);
x_721 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_720, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_719);
if (lean_obj_tag(x_721) == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_718);
lean_ctor_set(x_723, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_724 = l_Lean_Compiler_LCNF_Simp_simp(x_723, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_722);
if (lean_obj_tag(x_724) == 0)
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_724, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_724, 1);
lean_inc(x_726);
lean_dec(x_724);
x_671 = x_725;
x_672 = x_726;
goto block_698;
}
else
{
uint8_t x_727; 
lean_dec(x_667);
lean_dec(x_655);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_727 = !lean_is_exclusive(x_724);
if (x_727 == 0)
{
return x_724;
}
else
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_724, 0);
x_729 = lean_ctor_get(x_724, 1);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_724);
x_730 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
return x_730;
}
}
}
else
{
uint8_t x_731; 
lean_dec(x_718);
lean_dec(x_667);
lean_dec(x_655);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_731 = !lean_is_exclusive(x_721);
if (x_731 == 0)
{
return x_721;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_721, 0);
x_733 = lean_ctor_get(x_721, 1);
lean_inc(x_733);
lean_inc(x_732);
lean_dec(x_721);
x_734 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_734, 0, x_732);
lean_ctor_set(x_734, 1, x_733);
return x_734;
}
}
}
else
{
uint8_t x_735; 
lean_dec(x_667);
lean_dec(x_655);
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
x_735 = !lean_is_exclusive(x_717);
if (x_735 == 0)
{
return x_717;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_717, 0);
x_737 = lean_ctor_get(x_717, 1);
lean_inc(x_737);
lean_inc(x_736);
lean_dec(x_717);
x_738 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set(x_738, 1, x_737);
return x_738;
}
}
}
block_698:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_673 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_674 = lean_array_push(x_673, x_667);
x_675 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_676 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_674, x_671, x_675, x_6, x_7, x_8, x_9, x_672);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
lean_inc(x_677);
x_679 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_679, 0, x_677);
lean_closure_set(x_679, 1, x_673);
x_680 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_655, x_679, x_6, x_7, x_8, x_9, x_678);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_682 = lean_ctor_get(x_680, 0);
x_683 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_683, 0, x_677);
lean_ctor_set(x_683, 1, x_682);
if (lean_is_scalar(x_22)) {
 x_684 = lean_alloc_ctor(1, 1, 0);
} else {
 x_684 = x_22;
}
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_680, 0, x_684);
return x_680;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_685 = lean_ctor_get(x_680, 0);
x_686 = lean_ctor_get(x_680, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_680);
x_687 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_687, 0, x_677);
lean_ctor_set(x_687, 1, x_685);
if (lean_is_scalar(x_22)) {
 x_688 = lean_alloc_ctor(1, 1, 0);
} else {
 x_688 = x_22;
}
lean_ctor_set(x_688, 0, x_687);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_686);
return x_689;
}
}
else
{
uint8_t x_690; 
lean_dec(x_677);
lean_dec(x_22);
x_690 = !lean_is_exclusive(x_680);
if (x_690 == 0)
{
return x_680;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_680, 0);
x_692 = lean_ctor_get(x_680, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_680);
x_693 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_693, 0, x_691);
lean_ctor_set(x_693, 1, x_692);
return x_693;
}
}
}
else
{
uint8_t x_694; 
lean_dec(x_655);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_694 = !lean_is_exclusive(x_676);
if (x_694 == 0)
{
return x_676;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_676, 0);
x_696 = lean_ctor_get(x_676, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_676);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_662);
x_739 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_740 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_741 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_739, x_655, x_740, x_6, x_7, x_8, x_9, x_663);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_742 = lean_ctor_get(x_741, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_741, 1);
lean_inc(x_743);
lean_dec(x_741);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_744 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_742, x_6, x_7, x_8, x_9, x_743);
if (lean_obj_tag(x_744) == 0)
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_749; lean_object* x_750; 
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_ctor_get(x_745, 0);
lean_inc(x_747);
x_748 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_748 == 0)
{
lean_object* x_763; 
lean_dec(x_27);
lean_dec(x_23);
x_763 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_747, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_746);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_763, 1);
lean_inc(x_764);
lean_dec(x_763);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_765 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_764);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
lean_dec(x_765);
x_749 = x_766;
x_750 = x_767;
goto block_762;
}
else
{
uint8_t x_768; 
lean_dec(x_745);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_768 = !lean_is_exclusive(x_765);
if (x_768 == 0)
{
return x_765;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = lean_ctor_get(x_765, 0);
x_770 = lean_ctor_get(x_765, 1);
lean_inc(x_770);
lean_inc(x_769);
lean_dec(x_765);
x_771 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_771, 0, x_769);
lean_ctor_set(x_771, 1, x_770);
return x_771;
}
}
}
else
{
uint8_t x_772; 
lean_dec(x_745);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_772 = !lean_is_exclusive(x_763);
if (x_772 == 0)
{
return x_763;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = lean_ctor_get(x_763, 0);
x_774 = lean_ctor_get(x_763, 1);
lean_inc(x_774);
lean_inc(x_773);
lean_dec(x_763);
x_775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_775, 0, x_773);
lean_ctor_set(x_775, 1, x_774);
return x_775;
}
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_776 = lean_array_get_size(x_23);
x_777 = l_Array_toSubarray___rarg(x_23, x_27, x_776);
x_778 = l_Array_ofSubarray___rarg(x_777);
x_779 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_779, 0, x_747);
lean_ctor_set(x_779, 1, x_778);
x_780 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_781 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_779, x_780, x_6, x_7, x_8, x_9, x_746);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
lean_dec(x_781);
x_784 = lean_ctor_get(x_782, 0);
lean_inc(x_784);
x_785 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_784, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_783);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
lean_dec(x_785);
x_787 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_787, 0, x_782);
lean_ctor_set(x_787, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_788 = l_Lean_Compiler_LCNF_Simp_simp(x_787, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_786);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
x_749 = x_789;
x_750 = x_790;
goto block_762;
}
else
{
uint8_t x_791; 
lean_dec(x_745);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_791 = !lean_is_exclusive(x_788);
if (x_791 == 0)
{
return x_788;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_788, 0);
x_793 = lean_ctor_get(x_788, 1);
lean_inc(x_793);
lean_inc(x_792);
lean_dec(x_788);
x_794 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_794, 0, x_792);
lean_ctor_set(x_794, 1, x_793);
return x_794;
}
}
}
else
{
uint8_t x_795; 
lean_dec(x_782);
lean_dec(x_745);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_795 = !lean_is_exclusive(x_785);
if (x_795 == 0)
{
return x_785;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_796 = lean_ctor_get(x_785, 0);
x_797 = lean_ctor_get(x_785, 1);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_785);
x_798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_798, 0, x_796);
lean_ctor_set(x_798, 1, x_797);
return x_798;
}
}
}
else
{
uint8_t x_799; 
lean_dec(x_745);
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
x_799 = !lean_is_exclusive(x_781);
if (x_799 == 0)
{
return x_781;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_781, 0);
x_801 = lean_ctor_get(x_781, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_781);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
block_762:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; uint8_t x_755; 
x_751 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_751, 0, x_745);
x_752 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_753 = lean_array_push(x_752, x_751);
x_754 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_753, x_749, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_750);
lean_dec(x_753);
x_755 = !lean_is_exclusive(x_754);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; 
x_756 = lean_ctor_get(x_754, 0);
if (lean_is_scalar(x_22)) {
 x_757 = lean_alloc_ctor(1, 1, 0);
} else {
 x_757 = x_22;
}
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_754, 0, x_757);
return x_754;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_758 = lean_ctor_get(x_754, 0);
x_759 = lean_ctor_get(x_754, 1);
lean_inc(x_759);
lean_inc(x_758);
lean_dec(x_754);
if (lean_is_scalar(x_22)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_22;
}
lean_ctor_set(x_760, 0, x_758);
x_761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_761, 0, x_760);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
}
}
else
{
uint8_t x_803; 
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
x_803 = !lean_is_exclusive(x_744);
if (x_803 == 0)
{
return x_744;
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_744, 0);
x_805 = lean_ctor_get(x_744, 1);
lean_inc(x_805);
lean_inc(x_804);
lean_dec(x_744);
x_806 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_806, 0, x_804);
lean_ctor_set(x_806, 1, x_805);
return x_806;
}
}
}
else
{
uint8_t x_807; 
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
x_807 = !lean_is_exclusive(x_741);
if (x_807 == 0)
{
return x_741;
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_741, 0);
x_809 = lean_ctor_get(x_741, 1);
lean_inc(x_809);
lean_inc(x_808);
lean_dec(x_741);
x_810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set(x_810, 1, x_809);
return x_810;
}
}
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_33);
lean_dec(x_21);
x_811 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_656);
x_812 = lean_ctor_get(x_811, 1);
lean_inc(x_812);
lean_dec(x_811);
x_813 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_813, 0, x_3);
lean_closure_set(x_813, 1, x_4);
lean_closure_set(x_813, 2, x_5);
lean_closure_set(x_813, 3, x_27);
lean_closure_set(x_813, 4, x_24);
lean_closure_set(x_813, 5, x_26);
lean_closure_set(x_813, 6, x_2);
lean_closure_set(x_813, 7, x_23);
x_814 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_655, x_813, x_6, x_7, x_8, x_9, x_812);
if (lean_obj_tag(x_814) == 0)
{
uint8_t x_815; 
x_815 = !lean_is_exclusive(x_814);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; 
x_816 = lean_ctor_get(x_814, 0);
if (lean_is_scalar(x_22)) {
 x_817 = lean_alloc_ctor(1, 1, 0);
} else {
 x_817 = x_22;
}
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_814, 0, x_817);
return x_814;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_818 = lean_ctor_get(x_814, 0);
x_819 = lean_ctor_get(x_814, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_814);
if (lean_is_scalar(x_22)) {
 x_820 = lean_alloc_ctor(1, 1, 0);
} else {
 x_820 = x_22;
}
lean_ctor_set(x_820, 0, x_818);
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_819);
return x_821;
}
}
else
{
uint8_t x_822; 
lean_dec(x_22);
x_822 = !lean_is_exclusive(x_814);
if (x_822 == 0)
{
return x_814;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_814, 0);
x_824 = lean_ctor_get(x_814, 1);
lean_inc(x_824);
lean_inc(x_823);
lean_dec(x_814);
x_825 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
return x_825;
}
}
}
}
else
{
uint8_t x_826; 
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
x_826 = !lean_is_exclusive(x_654);
if (x_826 == 0)
{
return x_654;
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_827 = lean_ctor_get(x_654, 0);
x_828 = lean_ctor_get(x_654, 1);
lean_inc(x_828);
lean_inc(x_827);
lean_dec(x_654);
x_829 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_829, 0, x_827);
lean_ctor_set(x_829, 1, x_828);
return x_829;
}
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_830 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_652);
x_831 = lean_ctor_get(x_830, 1);
lean_inc(x_831);
lean_dec(x_830);
x_832 = l_Lean_Compiler_LCNF_Simp_simp(x_651, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_831);
if (lean_obj_tag(x_832) == 0)
{
uint8_t x_833; 
x_833 = !lean_is_exclusive(x_832);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; 
x_834 = lean_ctor_get(x_832, 0);
if (lean_is_scalar(x_22)) {
 x_835 = lean_alloc_ctor(1, 1, 0);
} else {
 x_835 = x_22;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_832, 0, x_835);
return x_832;
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_836 = lean_ctor_get(x_832, 0);
x_837 = lean_ctor_get(x_832, 1);
lean_inc(x_837);
lean_inc(x_836);
lean_dec(x_832);
if (lean_is_scalar(x_22)) {
 x_838 = lean_alloc_ctor(1, 1, 0);
} else {
 x_838 = x_22;
}
lean_ctor_set(x_838, 0, x_836);
x_839 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
}
else
{
uint8_t x_840; 
lean_dec(x_22);
x_840 = !lean_is_exclusive(x_832);
if (x_840 == 0)
{
return x_832;
}
else
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_841 = lean_ctor_get(x_832, 0);
x_842 = lean_ctor_get(x_832, 1);
lean_inc(x_842);
lean_inc(x_841);
lean_dec(x_832);
x_843 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_843, 0, x_841);
lean_ctor_set(x_843, 1, x_842);
return x_843;
}
}
}
}
}
else
{
uint8_t x_847; 
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
x_847 = !lean_is_exclusive(x_650);
if (x_847 == 0)
{
return x_650;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_848 = lean_ctor_get(x_650, 0);
x_849 = lean_ctor_get(x_650, 1);
lean_inc(x_849);
lean_inc(x_848);
lean_dec(x_650);
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_849);
return x_850;
}
}
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; uint8_t x_858; lean_object* x_859; 
x_851 = lean_ctor_get(x_3, 0);
x_852 = lean_ctor_get(x_3, 1);
x_853 = lean_ctor_get(x_3, 2);
x_854 = lean_ctor_get(x_3, 3);
lean_inc(x_854);
lean_inc(x_853);
lean_inc(x_852);
lean_inc(x_851);
lean_dec(x_3);
lean_inc(x_640);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_640);
lean_ctor_set(x_855, 1, x_853);
x_856 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_854, x_640, x_642);
x_857 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_857, 0, x_851);
lean_ctor_set(x_857, 1, x_852);
lean_ctor_set(x_857, 2, x_855);
lean_ctor_set(x_857, 3, x_856);
x_858 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_859 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_858, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_643);
lean_dec(x_29);
if (lean_obj_tag(x_859) == 0)
{
lean_object* x_860; lean_object* x_861; uint8_t x_862; uint8_t x_1045; 
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_859, 1);
lean_inc(x_861);
lean_dec(x_859);
x_1045 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1045 == 0)
{
x_862 = x_858;
goto block_1044;
}
else
{
uint8_t x_1046; 
x_1046 = lean_nat_dec_eq(x_24, x_27);
x_862 = x_1046;
goto block_1044;
}
block_1044:
{
if (x_862 == 0)
{
lean_object* x_863; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_857);
x_863 = l_Lean_Compiler_LCNF_Simp_simp(x_860, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_861);
if (lean_obj_tag(x_863) == 0)
{
lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_864 = lean_ctor_get(x_863, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_863, 1);
lean_inc(x_865);
lean_dec(x_863);
lean_inc(x_864);
x_866 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_864);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_867 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_865);
x_868 = lean_ctor_get(x_867, 1);
lean_inc(x_868);
lean_dec(x_867);
x_869 = lean_ctor_get(x_21, 2);
lean_inc(x_869);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_870 = l_Lean_Compiler_LCNF_inferAppType(x_869, x_33, x_6, x_7, x_8, x_9, x_868);
x_871 = lean_ctor_get(x_870, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_870, 1);
lean_inc(x_872);
lean_dec(x_870);
lean_inc(x_871);
x_873 = l_Lean_Expr_headBeta(x_871);
x_874 = l_Lean_Expr_isForall(x_873);
lean_dec(x_873);
if (x_874 == 0)
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; lean_object* x_880; lean_object* x_881; 
x_875 = l_Lean_Compiler_LCNF_mkAuxParam(x_871, x_858, x_6, x_7, x_8, x_9, x_872);
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = lean_ctor_get(x_876, 0);
lean_inc(x_878);
x_879 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_879 == 0)
{
lean_object* x_905; 
lean_dec(x_27);
lean_dec(x_23);
x_905 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_878, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_877);
if (lean_obj_tag(x_905) == 0)
{
lean_object* x_906; lean_object* x_907; 
x_906 = lean_ctor_get(x_905, 1);
lean_inc(x_906);
lean_dec(x_905);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_907 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_906);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
lean_dec(x_907);
x_880 = x_908;
x_881 = x_909;
goto block_904;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_876);
lean_dec(x_864);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_910 = lean_ctor_get(x_907, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_907, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_912 = x_907;
} else {
 lean_dec_ref(x_907);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_876);
lean_dec(x_864);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_914 = lean_ctor_get(x_905, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_905, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_905)) {
 lean_ctor_release(x_905, 0);
 lean_ctor_release(x_905, 1);
 x_916 = x_905;
} else {
 lean_dec_ref(x_905);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_914);
lean_ctor_set(x_917, 1, x_915);
return x_917;
}
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_918 = lean_array_get_size(x_23);
x_919 = l_Array_toSubarray___rarg(x_23, x_27, x_918);
x_920 = l_Array_ofSubarray___rarg(x_919);
x_921 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_921, 0, x_878);
lean_ctor_set(x_921, 1, x_920);
x_922 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_923 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_921, x_922, x_6, x_7, x_8, x_9, x_877);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
lean_dec(x_923);
x_926 = lean_ctor_get(x_924, 0);
lean_inc(x_926);
x_927 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_926, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_925);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_928 = lean_ctor_get(x_927, 1);
lean_inc(x_928);
lean_dec(x_927);
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_924);
lean_ctor_set(x_929, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_930 = l_Lean_Compiler_LCNF_Simp_simp(x_929, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_928);
if (lean_obj_tag(x_930) == 0)
{
lean_object* x_931; lean_object* x_932; 
x_931 = lean_ctor_get(x_930, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_930, 1);
lean_inc(x_932);
lean_dec(x_930);
x_880 = x_931;
x_881 = x_932;
goto block_904;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; 
lean_dec(x_876);
lean_dec(x_864);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_933 = lean_ctor_get(x_930, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_930, 1);
lean_inc(x_934);
if (lean_is_exclusive(x_930)) {
 lean_ctor_release(x_930, 0);
 lean_ctor_release(x_930, 1);
 x_935 = x_930;
} else {
 lean_dec_ref(x_930);
 x_935 = lean_box(0);
}
if (lean_is_scalar(x_935)) {
 x_936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_936 = x_935;
}
lean_ctor_set(x_936, 0, x_933);
lean_ctor_set(x_936, 1, x_934);
return x_936;
}
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
lean_dec(x_924);
lean_dec(x_876);
lean_dec(x_864);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_937 = lean_ctor_get(x_927, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_927, 1);
lean_inc(x_938);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_939 = x_927;
} else {
 lean_dec_ref(x_927);
 x_939 = lean_box(0);
}
if (lean_is_scalar(x_939)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_939;
}
lean_ctor_set(x_940, 0, x_937);
lean_ctor_set(x_940, 1, x_938);
return x_940;
}
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_876);
lean_dec(x_864);
lean_dec(x_857);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_941 = lean_ctor_get(x_923, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_923, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_943 = x_923;
} else {
 lean_dec_ref(x_923);
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
block_904:
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_882 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_883 = lean_array_push(x_882, x_876);
x_884 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_885 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_883, x_880, x_884, x_6, x_7, x_8, x_9, x_881);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_885, 1);
lean_inc(x_887);
lean_dec(x_885);
lean_inc(x_886);
x_888 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_888, 0, x_886);
lean_closure_set(x_888, 1, x_882);
x_889 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_864, x_888, x_6, x_7, x_8, x_9, x_887);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_892 = x_889;
} else {
 lean_dec_ref(x_889);
 x_892 = lean_box(0);
}
x_893 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_893, 0, x_886);
lean_ctor_set(x_893, 1, x_890);
if (lean_is_scalar(x_22)) {
 x_894 = lean_alloc_ctor(1, 1, 0);
} else {
 x_894 = x_22;
}
lean_ctor_set(x_894, 0, x_893);
if (lean_is_scalar(x_892)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_892;
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_891);
return x_895;
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_886);
lean_dec(x_22);
x_896 = lean_ctor_get(x_889, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_889, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_898 = x_889;
} else {
 lean_dec_ref(x_889);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_896);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
lean_dec(x_864);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_900 = lean_ctor_get(x_885, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_885, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_902 = x_885;
} else {
 lean_dec_ref(x_885);
 x_902 = lean_box(0);
}
if (lean_is_scalar(x_902)) {
 x_903 = lean_alloc_ctor(1, 2, 0);
} else {
 x_903 = x_902;
}
lean_ctor_set(x_903, 0, x_900);
lean_ctor_set(x_903, 1, x_901);
return x_903;
}
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; 
lean_dec(x_871);
x_945 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_946 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_947 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_945, x_864, x_946, x_6, x_7, x_8, x_9, x_872);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
lean_dec(x_947);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_950 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_948, x_6, x_7, x_8, x_9, x_949);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; lean_object* x_955; lean_object* x_956; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
x_953 = lean_ctor_get(x_951, 0);
lean_inc(x_953);
x_954 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_954 == 0)
{
lean_object* x_967; 
lean_dec(x_27);
lean_dec(x_23);
x_967 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_953, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_952);
if (lean_obj_tag(x_967) == 0)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_967, 1);
lean_inc(x_968);
lean_dec(x_967);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_857);
x_969 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_968);
if (lean_obj_tag(x_969) == 0)
{
lean_object* x_970; lean_object* x_971; 
x_970 = lean_ctor_get(x_969, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_969, 1);
lean_inc(x_971);
lean_dec(x_969);
x_955 = x_970;
x_956 = x_971;
goto block_966;
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_951);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_972 = lean_ctor_get(x_969, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_969, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_974 = x_969;
} else {
 lean_dec_ref(x_969);
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
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_951);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_976 = lean_ctor_get(x_967, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_967, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_978 = x_967;
} else {
 lean_dec_ref(x_967);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(1, 2, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_976);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_980 = lean_array_get_size(x_23);
x_981 = l_Array_toSubarray___rarg(x_23, x_27, x_980);
x_982 = l_Array_ofSubarray___rarg(x_981);
x_983 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_983, 0, x_953);
lean_ctor_set(x_983, 1, x_982);
x_984 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_985 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_983, x_984, x_6, x_7, x_8, x_9, x_952);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_986 = lean_ctor_get(x_985, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_985, 1);
lean_inc(x_987);
lean_dec(x_985);
x_988 = lean_ctor_get(x_986, 0);
lean_inc(x_988);
x_989 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_988, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_987);
if (lean_obj_tag(x_989) == 0)
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_989, 1);
lean_inc(x_990);
lean_dec(x_989);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_986);
lean_ctor_set(x_991, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_857);
x_992 = l_Lean_Compiler_LCNF_Simp_simp(x_991, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_990);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_ctor_get(x_992, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_992, 1);
lean_inc(x_994);
lean_dec(x_992);
x_955 = x_993;
x_956 = x_994;
goto block_966;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_951);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_995 = lean_ctor_get(x_992, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_992, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_997 = x_992;
} else {
 lean_dec_ref(x_992);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_986);
lean_dec(x_951);
lean_dec(x_857);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_999 = lean_ctor_get(x_989, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_989, 1);
lean_inc(x_1000);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_1001 = x_989;
} else {
 lean_dec_ref(x_989);
 x_1001 = lean_box(0);
}
if (lean_is_scalar(x_1001)) {
 x_1002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1002 = x_1001;
}
lean_ctor_set(x_1002, 0, x_999);
lean_ctor_set(x_1002, 1, x_1000);
return x_1002;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_951);
lean_dec(x_857);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1003 = lean_ctor_get(x_985, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_985, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_985)) {
 lean_ctor_release(x_985, 0);
 lean_ctor_release(x_985, 1);
 x_1005 = x_985;
} else {
 lean_dec_ref(x_985);
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
block_966:
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_957 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_957, 0, x_951);
x_958 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_959 = lean_array_push(x_958, x_957);
x_960 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_959, x_955, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_956);
lean_dec(x_959);
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_963 = x_960;
} else {
 lean_dec_ref(x_960);
 x_963 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_964 = lean_alloc_ctor(1, 1, 0);
} else {
 x_964 = x_22;
}
lean_ctor_set(x_964, 0, x_961);
if (lean_is_scalar(x_963)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_963;
}
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_962);
return x_965;
}
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_857);
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
x_1007 = lean_ctor_get(x_950, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_950, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_1009 = x_950;
} else {
 lean_dec_ref(x_950);
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
lean_dec(x_857);
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
x_1011 = lean_ctor_get(x_947, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_947, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_1013 = x_947;
} else {
 lean_dec_ref(x_947);
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
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_33);
lean_dec(x_21);
x_1015 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_865);
x_1016 = lean_ctor_get(x_1015, 1);
lean_inc(x_1016);
lean_dec(x_1015);
x_1017 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1017, 0, x_857);
lean_closure_set(x_1017, 1, x_4);
lean_closure_set(x_1017, 2, x_5);
lean_closure_set(x_1017, 3, x_27);
lean_closure_set(x_1017, 4, x_24);
lean_closure_set(x_1017, 5, x_26);
lean_closure_set(x_1017, 6, x_2);
lean_closure_set(x_1017, 7, x_23);
x_1018 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_864, x_1017, x_6, x_7, x_8, x_9, x_1016);
if (lean_obj_tag(x_1018) == 0)
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1018, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1021 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1021 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1022 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1022 = x_22;
}
lean_ctor_set(x_1022, 0, x_1019);
if (lean_is_scalar(x_1021)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_1021;
}
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1020);
return x_1023;
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_22);
x_1024 = lean_ctor_get(x_1018, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1018, 1);
lean_inc(x_1025);
if (lean_is_exclusive(x_1018)) {
 lean_ctor_release(x_1018, 0);
 lean_ctor_release(x_1018, 1);
 x_1026 = x_1018;
} else {
 lean_dec_ref(x_1018);
 x_1026 = lean_box(0);
}
if (lean_is_scalar(x_1026)) {
 x_1027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1027 = x_1026;
}
lean_ctor_set(x_1027, 0, x_1024);
lean_ctor_set(x_1027, 1, x_1025);
return x_1027;
}
}
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_857);
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
x_1028 = lean_ctor_get(x_863, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_863, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_863)) {
 lean_ctor_release(x_863, 0);
 lean_ctor_release(x_863, 1);
 x_1030 = x_863;
} else {
 lean_dec_ref(x_863);
 x_1030 = lean_box(0);
}
if (lean_is_scalar(x_1030)) {
 x_1031 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1031 = x_1030;
}
lean_ctor_set(x_1031, 0, x_1028);
lean_ctor_set(x_1031, 1, x_1029);
return x_1031;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_1032 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_861);
x_1033 = lean_ctor_get(x_1032, 1);
lean_inc(x_1033);
lean_dec(x_1032);
x_1034 = l_Lean_Compiler_LCNF_Simp_simp(x_860, x_857, x_4, x_5, x_6, x_7, x_8, x_9, x_1033);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
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
if (lean_is_scalar(x_22)) {
 x_1038 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1038 = x_22;
}
lean_ctor_set(x_1038, 0, x_1035);
if (lean_is_scalar(x_1037)) {
 x_1039 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1039 = x_1037;
}
lean_ctor_set(x_1039, 0, x_1038);
lean_ctor_set(x_1039, 1, x_1036);
return x_1039;
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
lean_dec(x_22);
x_1040 = lean_ctor_get(x_1034, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1034, 1);
lean_inc(x_1041);
if (lean_is_exclusive(x_1034)) {
 lean_ctor_release(x_1034, 0);
 lean_ctor_release(x_1034, 1);
 x_1042 = x_1034;
} else {
 lean_dec_ref(x_1034);
 x_1042 = lean_box(0);
}
if (lean_is_scalar(x_1042)) {
 x_1043 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1043 = x_1042;
}
lean_ctor_set(x_1043, 0, x_1040);
lean_ctor_set(x_1043, 1, x_1041);
return x_1043;
}
}
}
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
lean_dec(x_857);
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
x_1047 = lean_ctor_get(x_859, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_859, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_859)) {
 lean_ctor_release(x_859, 0);
 lean_ctor_release(x_859, 1);
 x_1049 = x_859;
} else {
 lean_dec_ref(x_859);
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
}
else
{
uint8_t x_1051; 
lean_dec(x_640);
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
x_1051 = !lean_is_exclusive(x_641);
if (x_1051 == 0)
{
return x_641;
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1052 = lean_ctor_get(x_641, 0);
x_1053 = lean_ctor_get(x_641, 1);
lean_inc(x_1053);
lean_inc(x_1052);
lean_dec(x_641);
x_1054 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
return x_1054;
}
}
}
default: 
{
lean_object* x_1055; uint8_t x_1056; lean_object* x_1057; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1055 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1055 = lean_box(0);
}
x_1056 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_33);
x_1057 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1056, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; uint8_t x_1060; uint8_t x_1252; 
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
lean_dec(x_1057);
x_1252 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1252 == 0)
{
x_1060 = x_1056;
goto block_1251;
}
else
{
uint8_t x_1253; 
x_1253 = lean_nat_dec_eq(x_24, x_27);
x_1060 = x_1253;
goto block_1251;
}
block_1251:
{
if (x_1060 == 0)
{
lean_object* x_1061; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1061 = l_Lean_Compiler_LCNF_Simp_simp(x_1058, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1059);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
lean_inc(x_1062);
x_1064 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1062);
if (x_1064 == 0)
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; uint8_t x_1072; 
x_1065 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1063);
x_1066 = lean_ctor_get(x_1065, 1);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_ctor_get(x_21, 2);
lean_inc(x_1067);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1068 = l_Lean_Compiler_LCNF_inferAppType(x_1067, x_33, x_6, x_7, x_8, x_9, x_1066);
x_1069 = lean_ctor_get(x_1068, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_1068, 1);
lean_inc(x_1070);
lean_dec(x_1068);
lean_inc(x_1069);
x_1071 = l_Lean_Expr_headBeta(x_1069);
x_1072 = l_Lean_Expr_isForall(x_1071);
lean_dec(x_1071);
if (x_1072 == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; uint8_t x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1073 = l_Lean_Compiler_LCNF_mkAuxParam(x_1069, x_1056, x_6, x_7, x_8, x_9, x_1070);
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1073, 1);
lean_inc(x_1075);
lean_dec(x_1073);
x_1076 = lean_ctor_get(x_1074, 0);
lean_inc(x_1076);
x_1077 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1077 == 0)
{
lean_object* x_1106; 
lean_dec(x_1055);
lean_dec(x_27);
lean_dec(x_23);
x_1106 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1076, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1075);
if (lean_obj_tag(x_1106) == 0)
{
lean_object* x_1107; lean_object* x_1108; 
x_1107 = lean_ctor_get(x_1106, 1);
lean_inc(x_1107);
lean_dec(x_1106);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1108 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1107);
if (lean_obj_tag(x_1108) == 0)
{
lean_object* x_1109; lean_object* x_1110; 
x_1109 = lean_ctor_get(x_1108, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1108, 1);
lean_inc(x_1110);
lean_dec(x_1108);
x_1078 = x_1109;
x_1079 = x_1110;
goto block_1105;
}
else
{
uint8_t x_1111; 
lean_dec(x_1074);
lean_dec(x_1062);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1111 = !lean_is_exclusive(x_1108);
if (x_1111 == 0)
{
return x_1108;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1108, 0);
x_1113 = lean_ctor_get(x_1108, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1108);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_1074);
lean_dec(x_1062);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1115 = !lean_is_exclusive(x_1106);
if (x_1115 == 0)
{
return x_1106;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1106, 0);
x_1117 = lean_ctor_get(x_1106, 1);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1106);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
return x_1118;
}
}
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1119 = lean_array_get_size(x_23);
x_1120 = l_Array_toSubarray___rarg(x_23, x_27, x_1119);
x_1121 = l_Array_ofSubarray___rarg(x_1120);
if (lean_is_scalar(x_1055)) {
 x_1122 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1122 = x_1055;
}
lean_ctor_set(x_1122, 0, x_1076);
lean_ctor_set(x_1122, 1, x_1121);
x_1123 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1124 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1122, x_1123, x_6, x_7, x_8, x_9, x_1075);
if (lean_obj_tag(x_1124) == 0)
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1125 = lean_ctor_get(x_1124, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_1124, 1);
lean_inc(x_1126);
lean_dec(x_1124);
x_1127 = lean_ctor_get(x_1125, 0);
lean_inc(x_1127);
x_1128 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1127, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1126);
if (lean_obj_tag(x_1128) == 0)
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1129 = lean_ctor_get(x_1128, 1);
lean_inc(x_1129);
lean_dec(x_1128);
x_1130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1130, 0, x_1125);
lean_ctor_set(x_1130, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1131 = l_Lean_Compiler_LCNF_Simp_simp(x_1130, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1129);
if (lean_obj_tag(x_1131) == 0)
{
lean_object* x_1132; lean_object* x_1133; 
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1131, 1);
lean_inc(x_1133);
lean_dec(x_1131);
x_1078 = x_1132;
x_1079 = x_1133;
goto block_1105;
}
else
{
uint8_t x_1134; 
lean_dec(x_1074);
lean_dec(x_1062);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1134 = !lean_is_exclusive(x_1131);
if (x_1134 == 0)
{
return x_1131;
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1135 = lean_ctor_get(x_1131, 0);
x_1136 = lean_ctor_get(x_1131, 1);
lean_inc(x_1136);
lean_inc(x_1135);
lean_dec(x_1131);
x_1137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set(x_1137, 1, x_1136);
return x_1137;
}
}
}
else
{
uint8_t x_1138; 
lean_dec(x_1125);
lean_dec(x_1074);
lean_dec(x_1062);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1138 = !lean_is_exclusive(x_1128);
if (x_1138 == 0)
{
return x_1128;
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1139 = lean_ctor_get(x_1128, 0);
x_1140 = lean_ctor_get(x_1128, 1);
lean_inc(x_1140);
lean_inc(x_1139);
lean_dec(x_1128);
x_1141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1141, 0, x_1139);
lean_ctor_set(x_1141, 1, x_1140);
return x_1141;
}
}
}
else
{
uint8_t x_1142; 
lean_dec(x_1074);
lean_dec(x_1062);
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
x_1142 = !lean_is_exclusive(x_1124);
if (x_1142 == 0)
{
return x_1124;
}
else
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1143 = lean_ctor_get(x_1124, 0);
x_1144 = lean_ctor_get(x_1124, 1);
lean_inc(x_1144);
lean_inc(x_1143);
lean_dec(x_1124);
x_1145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1144);
return x_1145;
}
}
}
block_1105:
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1080 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1081 = lean_array_push(x_1080, x_1074);
x_1082 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1083 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1081, x_1078, x_1082, x_6, x_7, x_8, x_9, x_1079);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec(x_1083);
lean_inc(x_1084);
x_1086 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1086, 0, x_1084);
lean_closure_set(x_1086, 1, x_1080);
x_1087 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1062, x_1086, x_6, x_7, x_8, x_9, x_1085);
if (lean_obj_tag(x_1087) == 0)
{
uint8_t x_1088; 
x_1088 = !lean_is_exclusive(x_1087);
if (x_1088 == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1089 = lean_ctor_get(x_1087, 0);
x_1090 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1090, 0, x_1084);
lean_ctor_set(x_1090, 1, x_1089);
if (lean_is_scalar(x_22)) {
 x_1091 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1091 = x_22;
}
lean_ctor_set(x_1091, 0, x_1090);
lean_ctor_set(x_1087, 0, x_1091);
return x_1087;
}
else
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; 
x_1092 = lean_ctor_get(x_1087, 0);
x_1093 = lean_ctor_get(x_1087, 1);
lean_inc(x_1093);
lean_inc(x_1092);
lean_dec(x_1087);
x_1094 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1094, 0, x_1084);
lean_ctor_set(x_1094, 1, x_1092);
if (lean_is_scalar(x_22)) {
 x_1095 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1095 = x_22;
}
lean_ctor_set(x_1095, 0, x_1094);
x_1096 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1096, 0, x_1095);
lean_ctor_set(x_1096, 1, x_1093);
return x_1096;
}
}
else
{
uint8_t x_1097; 
lean_dec(x_1084);
lean_dec(x_22);
x_1097 = !lean_is_exclusive(x_1087);
if (x_1097 == 0)
{
return x_1087;
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1098 = lean_ctor_get(x_1087, 0);
x_1099 = lean_ctor_get(x_1087, 1);
lean_inc(x_1099);
lean_inc(x_1098);
lean_dec(x_1087);
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
lean_dec(x_1062);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1101 = !lean_is_exclusive(x_1083);
if (x_1101 == 0)
{
return x_1083;
}
else
{
lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
x_1102 = lean_ctor_get(x_1083, 0);
x_1103 = lean_ctor_get(x_1083, 1);
lean_inc(x_1103);
lean_inc(x_1102);
lean_dec(x_1083);
x_1104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1104, 0, x_1102);
lean_ctor_set(x_1104, 1, x_1103);
return x_1104;
}
}
}
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
lean_dec(x_1069);
x_1146 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1147 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1148 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1146, x_1062, x_1147, x_6, x_7, x_8, x_9, x_1070);
if (lean_obj_tag(x_1148) == 0)
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1149 = lean_ctor_get(x_1148, 0);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_1148, 1);
lean_inc(x_1150);
lean_dec(x_1148);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1151 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1149, x_6, x_7, x_8, x_9, x_1150);
if (lean_obj_tag(x_1151) == 0)
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; uint8_t x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1152 = lean_ctor_get(x_1151, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1151, 1);
lean_inc(x_1153);
lean_dec(x_1151);
x_1154 = lean_ctor_get(x_1152, 0);
lean_inc(x_1154);
x_1155 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1155 == 0)
{
lean_object* x_1170; 
lean_dec(x_1055);
lean_dec(x_27);
lean_dec(x_23);
x_1170 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1153);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; 
x_1171 = lean_ctor_get(x_1170, 1);
lean_inc(x_1171);
lean_dec(x_1170);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1172 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1171);
if (lean_obj_tag(x_1172) == 0)
{
lean_object* x_1173; lean_object* x_1174; 
x_1173 = lean_ctor_get(x_1172, 0);
lean_inc(x_1173);
x_1174 = lean_ctor_get(x_1172, 1);
lean_inc(x_1174);
lean_dec(x_1172);
x_1156 = x_1173;
x_1157 = x_1174;
goto block_1169;
}
else
{
uint8_t x_1175; 
lean_dec(x_1152);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1175 = !lean_is_exclusive(x_1172);
if (x_1175 == 0)
{
return x_1172;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1172, 0);
x_1177 = lean_ctor_get(x_1172, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1172);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
return x_1178;
}
}
}
else
{
uint8_t x_1179; 
lean_dec(x_1152);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1179 = !lean_is_exclusive(x_1170);
if (x_1179 == 0)
{
return x_1170;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1170, 0);
x_1181 = lean_ctor_get(x_1170, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1170);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
else
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
x_1183 = lean_array_get_size(x_23);
x_1184 = l_Array_toSubarray___rarg(x_23, x_27, x_1183);
x_1185 = l_Array_ofSubarray___rarg(x_1184);
if (lean_is_scalar(x_1055)) {
 x_1186 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1186 = x_1055;
}
lean_ctor_set(x_1186, 0, x_1154);
lean_ctor_set(x_1186, 1, x_1185);
x_1187 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1188 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1186, x_1187, x_6, x_7, x_8, x_9, x_1153);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1189 = lean_ctor_get(x_1188, 0);
lean_inc(x_1189);
x_1190 = lean_ctor_get(x_1188, 1);
lean_inc(x_1190);
lean_dec(x_1188);
x_1191 = lean_ctor_get(x_1189, 0);
lean_inc(x_1191);
x_1192 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1191, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1190);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1193 = lean_ctor_get(x_1192, 1);
lean_inc(x_1193);
lean_dec(x_1192);
x_1194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1194, 0, x_1189);
lean_ctor_set(x_1194, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1195 = l_Lean_Compiler_LCNF_Simp_simp(x_1194, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1193);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
lean_dec(x_1195);
x_1156 = x_1196;
x_1157 = x_1197;
goto block_1169;
}
else
{
uint8_t x_1198; 
lean_dec(x_1152);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1198 = !lean_is_exclusive(x_1195);
if (x_1198 == 0)
{
return x_1195;
}
else
{
lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; 
x_1199 = lean_ctor_get(x_1195, 0);
x_1200 = lean_ctor_get(x_1195, 1);
lean_inc(x_1200);
lean_inc(x_1199);
lean_dec(x_1195);
x_1201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1201, 0, x_1199);
lean_ctor_set(x_1201, 1, x_1200);
return x_1201;
}
}
}
else
{
uint8_t x_1202; 
lean_dec(x_1189);
lean_dec(x_1152);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1202 = !lean_is_exclusive(x_1192);
if (x_1202 == 0)
{
return x_1192;
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1203 = lean_ctor_get(x_1192, 0);
x_1204 = lean_ctor_get(x_1192, 1);
lean_inc(x_1204);
lean_inc(x_1203);
lean_dec(x_1192);
x_1205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1205, 0, x_1203);
lean_ctor_set(x_1205, 1, x_1204);
return x_1205;
}
}
}
else
{
uint8_t x_1206; 
lean_dec(x_1152);
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
x_1206 = !lean_is_exclusive(x_1188);
if (x_1206 == 0)
{
return x_1188;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1207 = lean_ctor_get(x_1188, 0);
x_1208 = lean_ctor_get(x_1188, 1);
lean_inc(x_1208);
lean_inc(x_1207);
lean_dec(x_1188);
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1207);
lean_ctor_set(x_1209, 1, x_1208);
return x_1209;
}
}
}
block_1169:
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; uint8_t x_1162; 
x_1158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1158, 0, x_1152);
x_1159 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1160 = lean_array_push(x_1159, x_1158);
x_1161 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1160, x_1156, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1157);
lean_dec(x_1160);
x_1162 = !lean_is_exclusive(x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; lean_object* x_1164; 
x_1163 = lean_ctor_get(x_1161, 0);
if (lean_is_scalar(x_22)) {
 x_1164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1164 = x_22;
}
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1161, 0, x_1164);
return x_1161;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1165 = lean_ctor_get(x_1161, 0);
x_1166 = lean_ctor_get(x_1161, 1);
lean_inc(x_1166);
lean_inc(x_1165);
lean_dec(x_1161);
if (lean_is_scalar(x_22)) {
 x_1167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1167 = x_22;
}
lean_ctor_set(x_1167, 0, x_1165);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_1167);
lean_ctor_set(x_1168, 1, x_1166);
return x_1168;
}
}
}
else
{
uint8_t x_1210; 
lean_dec(x_1055);
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
x_1210 = !lean_is_exclusive(x_1151);
if (x_1210 == 0)
{
return x_1151;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1211 = lean_ctor_get(x_1151, 0);
x_1212 = lean_ctor_get(x_1151, 1);
lean_inc(x_1212);
lean_inc(x_1211);
lean_dec(x_1151);
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
lean_dec(x_1055);
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
x_1214 = !lean_is_exclusive(x_1148);
if (x_1214 == 0)
{
return x_1148;
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
x_1215 = lean_ctor_get(x_1148, 0);
x_1216 = lean_ctor_get(x_1148, 1);
lean_inc(x_1216);
lean_inc(x_1215);
lean_dec(x_1148);
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
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_1055);
lean_dec(x_33);
lean_dec(x_21);
x_1218 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1063);
x_1219 = lean_ctor_get(x_1218, 1);
lean_inc(x_1219);
lean_dec(x_1218);
x_1220 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2), 14, 8);
lean_closure_set(x_1220, 0, x_3);
lean_closure_set(x_1220, 1, x_4);
lean_closure_set(x_1220, 2, x_5);
lean_closure_set(x_1220, 3, x_27);
lean_closure_set(x_1220, 4, x_24);
lean_closure_set(x_1220, 5, x_26);
lean_closure_set(x_1220, 6, x_2);
lean_closure_set(x_1220, 7, x_23);
x_1221 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1062, x_1220, x_6, x_7, x_8, x_9, x_1219);
if (lean_obj_tag(x_1221) == 0)
{
uint8_t x_1222; 
x_1222 = !lean_is_exclusive(x_1221);
if (x_1222 == 0)
{
lean_object* x_1223; lean_object* x_1224; 
x_1223 = lean_ctor_get(x_1221, 0);
if (lean_is_scalar(x_22)) {
 x_1224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1224 = x_22;
}
lean_ctor_set(x_1224, 0, x_1223);
lean_ctor_set(x_1221, 0, x_1224);
return x_1221;
}
else
{
lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; 
x_1225 = lean_ctor_get(x_1221, 0);
x_1226 = lean_ctor_get(x_1221, 1);
lean_inc(x_1226);
lean_inc(x_1225);
lean_dec(x_1221);
if (lean_is_scalar(x_22)) {
 x_1227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1227 = x_22;
}
lean_ctor_set(x_1227, 0, x_1225);
x_1228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1228, 0, x_1227);
lean_ctor_set(x_1228, 1, x_1226);
return x_1228;
}
}
else
{
uint8_t x_1229; 
lean_dec(x_22);
x_1229 = !lean_is_exclusive(x_1221);
if (x_1229 == 0)
{
return x_1221;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1230 = lean_ctor_get(x_1221, 0);
x_1231 = lean_ctor_get(x_1221, 1);
lean_inc(x_1231);
lean_inc(x_1230);
lean_dec(x_1221);
x_1232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1232, 0, x_1230);
lean_ctor_set(x_1232, 1, x_1231);
return x_1232;
}
}
}
}
else
{
uint8_t x_1233; 
lean_dec(x_1055);
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
x_1233 = !lean_is_exclusive(x_1061);
if (x_1233 == 0)
{
return x_1061;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1061, 0);
x_1235 = lean_ctor_get(x_1061, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1061);
x_1236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1236, 0, x_1234);
lean_ctor_set(x_1236, 1, x_1235);
return x_1236;
}
}
}
else
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
lean_dec(x_1055);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_1237 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1059);
x_1238 = lean_ctor_get(x_1237, 1);
lean_inc(x_1238);
lean_dec(x_1237);
x_1239 = l_Lean_Compiler_LCNF_Simp_simp(x_1058, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1238);
if (lean_obj_tag(x_1239) == 0)
{
uint8_t x_1240; 
x_1240 = !lean_is_exclusive(x_1239);
if (x_1240 == 0)
{
lean_object* x_1241; lean_object* x_1242; 
x_1241 = lean_ctor_get(x_1239, 0);
if (lean_is_scalar(x_22)) {
 x_1242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1242 = x_22;
}
lean_ctor_set(x_1242, 0, x_1241);
lean_ctor_set(x_1239, 0, x_1242);
return x_1239;
}
else
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1243 = lean_ctor_get(x_1239, 0);
x_1244 = lean_ctor_get(x_1239, 1);
lean_inc(x_1244);
lean_inc(x_1243);
lean_dec(x_1239);
if (lean_is_scalar(x_22)) {
 x_1245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1245 = x_22;
}
lean_ctor_set(x_1245, 0, x_1243);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1245);
lean_ctor_set(x_1246, 1, x_1244);
return x_1246;
}
}
else
{
uint8_t x_1247; 
lean_dec(x_22);
x_1247 = !lean_is_exclusive(x_1239);
if (x_1247 == 0)
{
return x_1239;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; 
x_1248 = lean_ctor_get(x_1239, 0);
x_1249 = lean_ctor_get(x_1239, 1);
lean_inc(x_1249);
lean_inc(x_1248);
lean_dec(x_1239);
x_1250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1250, 0, x_1248);
lean_ctor_set(x_1250, 1, x_1249);
return x_1250;
}
}
}
}
}
else
{
uint8_t x_1254; 
lean_dec(x_1055);
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
x_1254 = !lean_is_exclusive(x_1057);
if (x_1254 == 0)
{
return x_1057;
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1255 = lean_ctor_get(x_1057, 0);
x_1256 = lean_ctor_get(x_1057, 1);
lean_inc(x_1256);
lean_inc(x_1255);
lean_dec(x_1057);
x_1257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1257, 0, x_1255);
lean_ctor_set(x_1257, 1, x_1256);
return x_1257;
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
lean_object* x_1258; lean_object* x_1259; 
x_1258 = lean_ctor_get(x_11, 0);
lean_inc(x_1258);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1258);
x_1259 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_1258, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1259) == 0)
{
lean_object* x_1260; lean_object* x_1261; uint8_t x_1262; 
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = !lean_is_exclusive(x_3);
if (x_1262 == 0)
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1263 = lean_ctor_get(x_3, 2);
x_1264 = lean_ctor_get(x_3, 3);
lean_inc(x_1258);
x_1265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1265, 0, x_1258);
lean_ctor_set(x_1265, 1, x_1263);
x_1266 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_1264, x_1258, x_1260);
lean_ctor_set(x_3, 3, x_1266);
lean_ctor_set(x_3, 2, x_1265);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1267 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1261);
if (lean_obj_tag(x_1267) == 0)
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1267, 1);
lean_inc(x_1269);
lean_dec(x_1267);
x_1270 = lean_ctor_get(x_1268, 0);
lean_inc(x_1270);
x_1271 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1270, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1269);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; 
x_1272 = lean_ctor_get(x_1271, 1);
lean_inc(x_1272);
lean_dec(x_1271);
x_1273 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1272);
x_1274 = lean_ctor_get(x_1273, 1);
lean_inc(x_1274);
lean_dec(x_1273);
x_1275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1275, 0, x_1268);
lean_ctor_set(x_1275, 1, x_2);
x_1276 = l_Lean_Compiler_LCNF_Simp_simp(x_1275, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1274);
if (lean_obj_tag(x_1276) == 0)
{
uint8_t x_1277; 
x_1277 = !lean_is_exclusive(x_1276);
if (x_1277 == 0)
{
lean_object* x_1278; lean_object* x_1279; 
x_1278 = lean_ctor_get(x_1276, 0);
if (lean_is_scalar(x_22)) {
 x_1279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1279 = x_22;
}
lean_ctor_set(x_1279, 0, x_1278);
lean_ctor_set(x_1276, 0, x_1279);
return x_1276;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1280 = lean_ctor_get(x_1276, 0);
x_1281 = lean_ctor_get(x_1276, 1);
lean_inc(x_1281);
lean_inc(x_1280);
lean_dec(x_1276);
if (lean_is_scalar(x_22)) {
 x_1282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1282 = x_22;
}
lean_ctor_set(x_1282, 0, x_1280);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_1282);
lean_ctor_set(x_1283, 1, x_1281);
return x_1283;
}
}
else
{
uint8_t x_1284; 
lean_dec(x_22);
x_1284 = !lean_is_exclusive(x_1276);
if (x_1284 == 0)
{
return x_1276;
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1285 = lean_ctor_get(x_1276, 0);
x_1286 = lean_ctor_get(x_1276, 1);
lean_inc(x_1286);
lean_inc(x_1285);
lean_dec(x_1276);
x_1287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1287, 0, x_1285);
lean_ctor_set(x_1287, 1, x_1286);
return x_1287;
}
}
}
else
{
uint8_t x_1288; 
lean_dec(x_1268);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1288 = !lean_is_exclusive(x_1271);
if (x_1288 == 0)
{
return x_1271;
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; 
x_1289 = lean_ctor_get(x_1271, 0);
x_1290 = lean_ctor_get(x_1271, 1);
lean_inc(x_1290);
lean_inc(x_1289);
lean_dec(x_1271);
x_1291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1291, 0, x_1289);
lean_ctor_set(x_1291, 1, x_1290);
return x_1291;
}
}
}
else
{
uint8_t x_1292; 
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
x_1292 = !lean_is_exclusive(x_1267);
if (x_1292 == 0)
{
return x_1267;
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1293 = lean_ctor_get(x_1267, 0);
x_1294 = lean_ctor_get(x_1267, 1);
lean_inc(x_1294);
lean_inc(x_1293);
lean_dec(x_1267);
x_1295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1295, 0, x_1293);
lean_ctor_set(x_1295, 1, x_1294);
return x_1295;
}
}
}
else
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1296 = lean_ctor_get(x_3, 0);
x_1297 = lean_ctor_get(x_3, 1);
x_1298 = lean_ctor_get(x_3, 2);
x_1299 = lean_ctor_get(x_3, 3);
lean_inc(x_1299);
lean_inc(x_1298);
lean_inc(x_1297);
lean_inc(x_1296);
lean_dec(x_3);
lean_inc(x_1258);
x_1300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1300, 0, x_1258);
lean_ctor_set(x_1300, 1, x_1298);
x_1301 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_Simp_withInlining___spec__1(x_1299, x_1258, x_1260);
x_1302 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1302, 0, x_1296);
lean_ctor_set(x_1302, 1, x_1297);
lean_ctor_set(x_1302, 2, x_1300);
lean_ctor_set(x_1302, 3, x_1301);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1303 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_1302, x_4, x_5, x_6, x_7, x_8, x_9, x_1261);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; 
x_1304 = lean_ctor_get(x_1303, 0);
lean_inc(x_1304);
x_1305 = lean_ctor_get(x_1303, 1);
lean_inc(x_1305);
lean_dec(x_1303);
x_1306 = lean_ctor_get(x_1304, 0);
lean_inc(x_1306);
x_1307 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1306, x_1302, x_4, x_5, x_6, x_7, x_8, x_9, x_1305);
if (lean_obj_tag(x_1307) == 0)
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1308 = lean_ctor_get(x_1307, 1);
lean_inc(x_1308);
lean_dec(x_1307);
x_1309 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1308);
x_1310 = lean_ctor_get(x_1309, 1);
lean_inc(x_1310);
lean_dec(x_1309);
x_1311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1311, 0, x_1304);
lean_ctor_set(x_1311, 1, x_2);
x_1312 = l_Lean_Compiler_LCNF_Simp_simp(x_1311, x_1302, x_4, x_5, x_6, x_7, x_8, x_9, x_1310);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
x_1314 = lean_ctor_get(x_1312, 1);
lean_inc(x_1314);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 lean_ctor_release(x_1312, 1);
 x_1315 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1315 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1316 = x_22;
}
lean_ctor_set(x_1316, 0, x_1313);
if (lean_is_scalar(x_1315)) {
 x_1317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1317 = x_1315;
}
lean_ctor_set(x_1317, 0, x_1316);
lean_ctor_set(x_1317, 1, x_1314);
return x_1317;
}
else
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
lean_dec(x_22);
x_1318 = lean_ctor_get(x_1312, 0);
lean_inc(x_1318);
x_1319 = lean_ctor_get(x_1312, 1);
lean_inc(x_1319);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 lean_ctor_release(x_1312, 1);
 x_1320 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1320 = lean_box(0);
}
if (lean_is_scalar(x_1320)) {
 x_1321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1321 = x_1320;
}
lean_ctor_set(x_1321, 0, x_1318);
lean_ctor_set(x_1321, 1, x_1319);
return x_1321;
}
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; 
lean_dec(x_1304);
lean_dec(x_1302);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1322 = lean_ctor_get(x_1307, 0);
lean_inc(x_1322);
x_1323 = lean_ctor_get(x_1307, 1);
lean_inc(x_1323);
if (lean_is_exclusive(x_1307)) {
 lean_ctor_release(x_1307, 0);
 lean_ctor_release(x_1307, 1);
 x_1324 = x_1307;
} else {
 lean_dec_ref(x_1307);
 x_1324 = lean_box(0);
}
if (lean_is_scalar(x_1324)) {
 x_1325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1325 = x_1324;
}
lean_ctor_set(x_1325, 0, x_1322);
lean_ctor_set(x_1325, 1, x_1323);
return x_1325;
}
}
else
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
lean_dec(x_1302);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1326 = lean_ctor_get(x_1303, 0);
lean_inc(x_1326);
x_1327 = lean_ctor_get(x_1303, 1);
lean_inc(x_1327);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 lean_ctor_release(x_1303, 1);
 x_1328 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1328 = lean_box(0);
}
if (lean_is_scalar(x_1328)) {
 x_1329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1329 = x_1328;
}
lean_ctor_set(x_1329, 0, x_1326);
lean_ctor_set(x_1329, 1, x_1327);
return x_1329;
}
}
}
else
{
uint8_t x_1330; 
lean_dec(x_1258);
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
x_1330 = !lean_is_exclusive(x_1259);
if (x_1330 == 0)
{
return x_1259;
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; 
x_1331 = lean_ctor_get(x_1259, 0);
x_1332 = lean_ctor_get(x_1259, 1);
lean_inc(x_1332);
lean_inc(x_1331);
lean_dec(x_1259);
x_1333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1333, 0, x_1331);
lean_ctor_set(x_1333, 1, x_1332);
return x_1333;
}
}
}
else
{
lean_object* x_1334; 
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1334 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1334) == 0)
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1335 = lean_ctor_get(x_1334, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1334, 1);
lean_inc(x_1336);
lean_dec(x_1334);
x_1337 = lean_ctor_get(x_1335, 0);
lean_inc(x_1337);
x_1338 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1337, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1336);
if (lean_obj_tag(x_1338) == 0)
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; 
x_1339 = lean_ctor_get(x_1338, 1);
lean_inc(x_1339);
lean_dec(x_1338);
x_1340 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1339);
x_1341 = lean_ctor_get(x_1340, 1);
lean_inc(x_1341);
lean_dec(x_1340);
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1335);
lean_ctor_set(x_1342, 1, x_2);
x_1343 = l_Lean_Compiler_LCNF_Simp_simp(x_1342, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1341);
if (lean_obj_tag(x_1343) == 0)
{
uint8_t x_1344; 
x_1344 = !lean_is_exclusive(x_1343);
if (x_1344 == 0)
{
lean_object* x_1345; lean_object* x_1346; 
x_1345 = lean_ctor_get(x_1343, 0);
if (lean_is_scalar(x_22)) {
 x_1346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1346 = x_22;
}
lean_ctor_set(x_1346, 0, x_1345);
lean_ctor_set(x_1343, 0, x_1346);
return x_1343;
}
else
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1347 = lean_ctor_get(x_1343, 0);
x_1348 = lean_ctor_get(x_1343, 1);
lean_inc(x_1348);
lean_inc(x_1347);
lean_dec(x_1343);
if (lean_is_scalar(x_22)) {
 x_1349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1349 = x_22;
}
lean_ctor_set(x_1349, 0, x_1347);
x_1350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1350, 0, x_1349);
lean_ctor_set(x_1350, 1, x_1348);
return x_1350;
}
}
else
{
uint8_t x_1351; 
lean_dec(x_22);
x_1351 = !lean_is_exclusive(x_1343);
if (x_1351 == 0)
{
return x_1343;
}
else
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1352 = lean_ctor_get(x_1343, 0);
x_1353 = lean_ctor_get(x_1343, 1);
lean_inc(x_1353);
lean_inc(x_1352);
lean_dec(x_1343);
x_1354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1354, 0, x_1352);
lean_ctor_set(x_1354, 1, x_1353);
return x_1354;
}
}
}
else
{
uint8_t x_1355; 
lean_dec(x_1335);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1355 = !lean_is_exclusive(x_1338);
if (x_1355 == 0)
{
return x_1338;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; 
x_1356 = lean_ctor_get(x_1338, 0);
x_1357 = lean_ctor_get(x_1338, 1);
lean_inc(x_1357);
lean_inc(x_1356);
lean_dec(x_1338);
x_1358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1358, 0, x_1356);
lean_ctor_set(x_1358, 1, x_1357);
return x_1358;
}
}
}
else
{
uint8_t x_1359; 
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
x_1359 = !lean_is_exclusive(x_1334);
if (x_1359 == 0)
{
return x_1334;
}
else
{
lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; 
x_1360 = lean_ctor_get(x_1334, 0);
x_1361 = lean_ctor_get(x_1334, 1);
lean_inc(x_1361);
lean_inc(x_1360);
lean_dec(x_1334);
x_1362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1362, 0, x_1360);
lean_ctor_set(x_1362, 1, x_1361);
return x_1362;
}
}
}
}
}
}
else
{
uint8_t x_1363; 
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
x_1363 = !lean_is_exclusive(x_12);
if (x_1363 == 0)
{
return x_12;
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1364 = lean_ctor_get(x_12, 0);
x_1365 = lean_ctor_get(x_12, 1);
lean_inc(x_1365);
lean_inc(x_1364);
lean_dec(x_12);
x_1366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1366, 0, x_1364);
lean_ctor_set(x_1366, 1, x_1365);
return x_1366;
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
uint8_t x_60; 
lean_dec(x_14);
x_60 = 0;
x_17 = x_60;
x_18 = x_10;
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_14, x_14);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_14);
x_62 = 0;
x_17 = x_62;
x_18 = x_10;
goto block_59;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_65 = l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(x_12, x_63, x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_17 = x_68;
x_18 = x_67;
goto block_59;
}
}
block_59:
{
uint8_t x_19; 
if (lean_obj_tag(x_13) == 6)
{
uint8_t x_58; 
x_58 = 0;
x_19 = x_58;
goto block_57;
}
else
{
x_19 = x_17;
goto block_57;
}
block_57:
{
if (x_19 == 0)
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
lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_2, 0);
lean_inc(x_69);
x_70 = l_Lean_Compiler_LCNF_Simp_simp(x_69, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_72);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_2, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
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
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_80 = lean_st_ref_get(x_3, x_70);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Compiler_LCNF_normFunDeclImp(x_84, x_64, x_83, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_88 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_86, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_71, x_89, x_92, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_93);
lean_dec(x_92);
return x_94;
}
else
{
uint8_t x_95; 
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_85, 0);
x_101 = lean_ctor_get(x_85, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_85);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_67, 1);
lean_inc(x_103);
lean_dec(x_67);
x_104 = lean_st_ref_get(x_3, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_108 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_64);
x_109 = l_Lean_Compiler_LCNF_normFunDeclImp(x_108, x_64, x_107, x_5, x_6, x_7, x_8, x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = lean_unbox(x_68);
lean_dec(x_68);
x_114 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_65, x_64, x_1, x_113, x_110, x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
return x_114;
}
else
{
uint8_t x_115; 
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
x_115 = !lean_is_exclusive(x_109);
if (x_115 == 0)
{
return x_109;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_109, 0);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_109);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
case 2:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_119 = lean_ctor_get(x_36, 1);
lean_inc(x_119);
lean_dec(x_36);
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
lean_inc(x_1);
lean_inc(x_120);
x_127 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 14, 4);
lean_closure_set(x_127, 0, x_121);
lean_closure_set(x_127, 1, x_120);
lean_closure_set(x_127, 2, x_1);
lean_closure_set(x_127, 3, x_124);
x_128 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_box(0);
x_130 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_127, x_120, x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_126);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_120, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_120, 2);
lean_inc(x_132);
x_133 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_131, x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_box(0);
x_135 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_127, x_120, x_134, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_126);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; 
x_136 = lean_st_ref_get(x_3, x_126);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_141 = l_Lean_Compiler_LCNF_normFunDeclImp(x_140, x_120, x_139, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_144 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_142, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_146);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_127, x_145, x_148, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_149);
lean_dec(x_148);
return x_150;
}
else
{
uint8_t x_151; 
lean_dec(x_127);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = !lean_is_exclusive(x_144);
if (x_151 == 0)
{
return x_144;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_144, 0);
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_144);
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
lean_dec(x_127);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_141);
if (x_155 == 0)
{
return x_141;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_141, 0);
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_141);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_123, 1);
lean_inc(x_159);
lean_dec(x_123);
x_160 = lean_st_ref_get(x_3, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_120);
x_165 = l_Lean_Compiler_LCNF_normFunDeclImp(x_164, x_120, x_163, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_box(0);
x_169 = lean_unbox(x_124);
lean_dec(x_124);
x_170 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_121, x_120, x_1, x_169, x_166, x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_167);
return x_170;
}
else
{
uint8_t x_171; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_165);
if (x_171 == 0)
{
return x_165;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_165, 0);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_165);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
case 3:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_36, 1);
lean_inc(x_175);
lean_dec(x_36);
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc(x_177);
x_178 = lean_st_ref_get(x_3, x_175);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_182 = 0;
lean_inc(x_176);
x_183 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_181, x_176, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_208; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec(x_183);
lean_inc(x_177);
x_185 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_182, x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_180);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_186);
lean_inc(x_184);
x_208 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_184, x_186, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_187);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_184);
x_211 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_184, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_array_get_size(x_186);
x_214 = lean_unsigned_to_nat(0u);
x_215 = lean_nat_dec_lt(x_214, x_213);
if (x_215 == 0)
{
lean_dec(x_213);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = x_212;
goto block_207;
}
else
{
uint8_t x_216; 
x_216 = lean_nat_dec_le(x_213, x_213);
if (x_216 == 0)
{
lean_dec(x_213);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_189 = x_212;
goto block_207;
}
else
{
size_t x_217; size_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_217 = 0;
x_218 = lean_usize_of_nat(x_213);
lean_dec(x_213);
x_219 = lean_box(0);
x_220 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_186, x_217, x_218, x_219, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_212);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_189 = x_221;
goto block_207;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_1);
x_222 = lean_ctor_get(x_208, 1);
lean_inc(x_222);
lean_dec(x_208);
x_223 = lean_ctor_get(x_209, 0);
lean_inc(x_223);
lean_dec(x_209);
x_1 = x_223;
x_9 = x_222;
goto _start;
}
}
else
{
uint8_t x_225; 
lean_dec(x_188);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
return x_208;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_208);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
block_207:
{
uint8_t x_190; 
x_190 = lean_name_eq(x_176, x_184);
lean_dec(x_176);
if (x_190 == 0)
{
uint8_t x_191; 
lean_dec(x_177);
x_191 = !lean_is_exclusive(x_1);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_1, 1);
lean_dec(x_192);
x_193 = lean_ctor_get(x_1, 0);
lean_dec(x_193);
lean_ctor_set(x_1, 1, x_186);
lean_ctor_set(x_1, 0, x_184);
if (lean_is_scalar(x_188)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_188;
}
lean_ctor_set(x_194, 0, x_1);
lean_ctor_set(x_194, 1, x_189);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_1);
x_195 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_186);
if (lean_is_scalar(x_188)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_188;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_189);
return x_196;
}
}
else
{
size_t x_197; size_t x_198; uint8_t x_199; 
x_197 = lean_ptr_addr(x_177);
lean_dec(x_177);
x_198 = lean_ptr_addr(x_186);
x_199 = lean_usize_dec_eq(x_197, x_198);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_1);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_1, 1);
lean_dec(x_201);
x_202 = lean_ctor_get(x_1, 0);
lean_dec(x_202);
lean_ctor_set(x_1, 1, x_186);
lean_ctor_set(x_1, 0, x_184);
if (lean_is_scalar(x_188)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_188;
}
lean_ctor_set(x_203, 0, x_1);
lean_ctor_set(x_203, 1, x_189);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_1);
x_204 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_204, 0, x_184);
lean_ctor_set(x_204, 1, x_186);
if (lean_is_scalar(x_188)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_188;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_189);
return x_205;
}
}
else
{
lean_object* x_206; 
lean_dec(x_186);
lean_dec(x_184);
if (lean_is_scalar(x_188)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_188;
}
lean_ctor_set(x_206, 0, x_1);
lean_ctor_set(x_206, 1, x_189);
return x_206;
}
}
}
}
else
{
lean_object* x_229; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_180);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_229;
}
}
case 4:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_36, 1);
lean_inc(x_230);
lean_dec(x_36);
x_231 = lean_ctor_get(x_1, 0);
lean_inc(x_231);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_231);
x_232 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_231, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 2);
lean_inc(x_237);
x_238 = lean_ctor_get(x_231, 3);
lean_inc(x_238);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 lean_ctor_release(x_231, 2);
 lean_ctor_release(x_231, 3);
 x_239 = x_231;
} else {
 lean_dec_ref(x_231);
 x_239 = lean_box(0);
}
x_240 = lean_st_ref_get(x_3, x_234);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = 0;
lean_inc(x_237);
x_245 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_243, x_237, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_st_ref_get(x_3, x_242);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_236);
x_251 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_250, x_244, x_236);
lean_inc(x_246);
x_252 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_249);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
lean_inc(x_246);
x_254 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7), 10, 1);
lean_closure_set(x_254, 0, x_246);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_238);
x_255 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_238, x_254, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_253);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; uint8_t x_303; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
x_262 = lean_array_get_size(x_259);
x_303 = lean_nat_dec_eq(x_262, x_34);
if (x_303 == 0)
{
x_263 = x_244;
goto block_302;
}
else
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_unsigned_to_nat(0u);
x_305 = lean_nat_dec_lt(x_304, x_262);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_307 = l___private_Init_Util_0__outOfBounds___rarg(x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_dec(x_307);
x_263 = x_244;
goto block_302;
}
else
{
uint8_t x_308; 
lean_dec(x_307);
x_308 = 1;
x_263 = x_308;
goto block_302;
}
}
else
{
lean_object* x_309; 
x_309 = lean_array_fget(x_259, x_304);
if (lean_obj_tag(x_309) == 0)
{
lean_dec(x_309);
x_263 = x_244;
goto block_302;
}
else
{
uint8_t x_310; 
lean_dec(x_309);
x_310 = 1;
x_263 = x_310;
goto block_302;
}
}
}
block_302:
{
if (x_263 == 0)
{
size_t x_264; size_t x_265; uint8_t x_266; 
lean_dec(x_262);
x_264 = lean_ptr_addr(x_238);
lean_dec(x_238);
x_265 = lean_ptr_addr(x_259);
x_266 = lean_usize_dec_eq(x_264, x_265);
if (x_266 == 0)
{
uint8_t x_267; 
lean_dec(x_237);
lean_dec(x_236);
x_267 = !lean_is_exclusive(x_1);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_1, 0);
lean_dec(x_268);
if (lean_is_scalar(x_239)) {
 x_269 = lean_alloc_ctor(0, 4, 0);
} else {
 x_269 = x_239;
}
lean_ctor_set(x_269, 0, x_235);
lean_ctor_set(x_269, 1, x_251);
lean_ctor_set(x_269, 2, x_246);
lean_ctor_set(x_269, 3, x_259);
lean_ctor_set(x_1, 0, x_269);
if (lean_is_scalar(x_261)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_261;
}
lean_ctor_set(x_270, 0, x_1);
lean_ctor_set(x_270, 1, x_260);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_1);
if (lean_is_scalar(x_239)) {
 x_271 = lean_alloc_ctor(0, 4, 0);
} else {
 x_271 = x_239;
}
lean_ctor_set(x_271, 0, x_235);
lean_ctor_set(x_271, 1, x_251);
lean_ctor_set(x_271, 2, x_246);
lean_ctor_set(x_271, 3, x_259);
x_272 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_272, 0, x_271);
if (lean_is_scalar(x_261)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_261;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_260);
return x_273;
}
}
else
{
size_t x_274; size_t x_275; uint8_t x_276; 
x_274 = lean_ptr_addr(x_236);
lean_dec(x_236);
x_275 = lean_ptr_addr(x_251);
x_276 = lean_usize_dec_eq(x_274, x_275);
if (x_276 == 0)
{
uint8_t x_277; 
lean_dec(x_237);
x_277 = !lean_is_exclusive(x_1);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_1, 0);
lean_dec(x_278);
if (lean_is_scalar(x_239)) {
 x_279 = lean_alloc_ctor(0, 4, 0);
} else {
 x_279 = x_239;
}
lean_ctor_set(x_279, 0, x_235);
lean_ctor_set(x_279, 1, x_251);
lean_ctor_set(x_279, 2, x_246);
lean_ctor_set(x_279, 3, x_259);
lean_ctor_set(x_1, 0, x_279);
if (lean_is_scalar(x_261)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_261;
}
lean_ctor_set(x_280, 0, x_1);
lean_ctor_set(x_280, 1, x_260);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_1);
if (lean_is_scalar(x_239)) {
 x_281 = lean_alloc_ctor(0, 4, 0);
} else {
 x_281 = x_239;
}
lean_ctor_set(x_281, 0, x_235);
lean_ctor_set(x_281, 1, x_251);
lean_ctor_set(x_281, 2, x_246);
lean_ctor_set(x_281, 3, x_259);
x_282 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_282, 0, x_281);
if (lean_is_scalar(x_261)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_261;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_260);
return x_283;
}
}
else
{
uint8_t x_284; 
x_284 = lean_name_eq(x_237, x_246);
lean_dec(x_237);
if (x_284 == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_1);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_1, 0);
lean_dec(x_286);
if (lean_is_scalar(x_239)) {
 x_287 = lean_alloc_ctor(0, 4, 0);
} else {
 x_287 = x_239;
}
lean_ctor_set(x_287, 0, x_235);
lean_ctor_set(x_287, 1, x_251);
lean_ctor_set(x_287, 2, x_246);
lean_ctor_set(x_287, 3, x_259);
lean_ctor_set(x_1, 0, x_287);
if (lean_is_scalar(x_261)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_261;
}
lean_ctor_set(x_288, 0, x_1);
lean_ctor_set(x_288, 1, x_260);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_1);
if (lean_is_scalar(x_239)) {
 x_289 = lean_alloc_ctor(0, 4, 0);
} else {
 x_289 = x_239;
}
lean_ctor_set(x_289, 0, x_235);
lean_ctor_set(x_289, 1, x_251);
lean_ctor_set(x_289, 2, x_246);
lean_ctor_set(x_289, 3, x_259);
x_290 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_290, 0, x_289);
if (lean_is_scalar(x_261)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_261;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_260);
return x_291;
}
}
else
{
lean_object* x_292; 
lean_dec(x_259);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_235);
if (lean_is_scalar(x_261)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_261;
}
lean_ctor_set(x_292, 0, x_1);
lean_ctor_set(x_292, 1, x_260);
return x_292;
}
}
}
}
else
{
lean_object* x_293; uint8_t x_294; 
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_1);
x_293 = lean_unsigned_to_nat(0u);
x_294 = lean_nat_dec_lt(x_293, x_262);
lean_dec(x_262);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_259);
x_295 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_296 = l___private_Init_Util_0__outOfBounds___rarg(x_295);
x_297 = l_Lean_Compiler_LCNF_AltCore_getCode(x_296);
lean_dec(x_296);
if (lean_is_scalar(x_261)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_261;
}
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_260);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_array_fget(x_259, x_293);
lean_dec(x_259);
x_300 = l_Lean_Compiler_LCNF_AltCore_getCode(x_299);
lean_dec(x_299);
if (lean_is_scalar(x_261)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_261;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_260);
return x_301;
}
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_258);
if (x_311 == 0)
{
return x_258;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_258, 0);
x_313 = lean_ctor_get(x_258, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_258);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_315 = !lean_is_exclusive(x_255);
if (x_315 == 0)
{
return x_255;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_255, 0);
x_317 = lean_ctor_get(x_255, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_255);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
else
{
lean_object* x_319; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_319 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_242);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_319;
}
}
else
{
uint8_t x_320; 
lean_dec(x_231);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_232);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_232, 0);
lean_dec(x_321);
x_322 = lean_ctor_get(x_233, 0);
lean_inc(x_322);
lean_dec(x_233);
lean_ctor_set(x_232, 0, x_322);
return x_232;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_232, 1);
lean_inc(x_323);
lean_dec(x_232);
x_324 = lean_ctor_get(x_233, 0);
lean_inc(x_324);
lean_dec(x_233);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
else
{
uint8_t x_326; 
lean_dec(x_231);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_326 = !lean_is_exclusive(x_232);
if (x_326 == 0)
{
return x_232;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_232, 0);
x_328 = lean_ctor_get(x_232, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_232);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
case 5:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; 
x_330 = lean_ctor_get(x_36, 1);
lean_inc(x_330);
lean_dec(x_36);
x_331 = lean_ctor_get(x_1, 0);
lean_inc(x_331);
x_332 = lean_st_ref_get(x_3, x_330);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
lean_dec(x_333);
x_336 = 0;
lean_inc(x_331);
x_337 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_335, x_331, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
lean_dec(x_337);
lean_inc(x_338);
x_339 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_338, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_334);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_340 = !lean_is_exclusive(x_339);
if (x_340 == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_339, 0);
lean_dec(x_341);
x_342 = lean_name_eq(x_331, x_338);
lean_dec(x_331);
if (x_342 == 0)
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_1);
if (x_343 == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_1, 0);
lean_dec(x_344);
lean_ctor_set(x_1, 0, x_338);
lean_ctor_set(x_339, 0, x_1);
return x_339;
}
else
{
lean_object* x_345; 
lean_dec(x_1);
x_345 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_339, 0, x_345);
return x_339;
}
}
else
{
lean_dec(x_338);
lean_ctor_set(x_339, 0, x_1);
return x_339;
}
}
else
{
lean_object* x_346; uint8_t x_347; 
x_346 = lean_ctor_get(x_339, 1);
lean_inc(x_346);
lean_dec(x_339);
x_347 = lean_name_eq(x_331, x_338);
lean_dec(x_331);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_348 = x_1;
} else {
 lean_dec_ref(x_1);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(5, 1, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_338);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_346);
return x_350;
}
else
{
lean_object* x_351; 
lean_dec(x_338);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_1);
lean_ctor_set(x_351, 1, x_346);
return x_351;
}
}
}
else
{
lean_object* x_352; 
lean_dec(x_331);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_334);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_352;
}
}
default: 
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_353 = lean_ctor_get(x_36, 1);
lean_inc(x_353);
lean_dec(x_36);
x_354 = lean_ctor_get(x_1, 0);
lean_inc(x_354);
x_355 = lean_st_ref_get(x_3, x_353);
lean_dec(x_3);
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; size_t x_361; size_t x_362; uint8_t x_363; 
x_357 = lean_ctor_get(x_355, 0);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
lean_dec(x_357);
x_359 = 0;
lean_inc(x_354);
x_360 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_358, x_359, x_354);
x_361 = lean_ptr_addr(x_354);
lean_dec(x_354);
x_362 = lean_ptr_addr(x_360);
x_363 = lean_usize_dec_eq(x_361, x_362);
if (x_363 == 0)
{
uint8_t x_364; 
x_364 = !lean_is_exclusive(x_1);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_1, 0);
lean_dec(x_365);
lean_ctor_set(x_1, 0, x_360);
lean_ctor_set(x_355, 0, x_1);
return x_355;
}
else
{
lean_object* x_366; 
lean_dec(x_1);
x_366 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_366, 0, x_360);
lean_ctor_set(x_355, 0, x_366);
return x_355;
}
}
else
{
lean_dec(x_360);
lean_ctor_set(x_355, 0, x_1);
return x_355;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; size_t x_372; size_t x_373; uint8_t x_374; 
x_367 = lean_ctor_get(x_355, 0);
x_368 = lean_ctor_get(x_355, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_355);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
lean_dec(x_367);
x_370 = 0;
lean_inc(x_354);
x_371 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_369, x_370, x_354);
x_372 = lean_ptr_addr(x_354);
lean_dec(x_354);
x_373 = lean_ptr_addr(x_371);
x_374 = lean_usize_dec_eq(x_372, x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_375 = x_1;
} else {
 lean_dec_ref(x_1);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(6, 1, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_371);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_368);
return x_377;
}
else
{
lean_object* x_378; 
lean_dec(x_371);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_1);
lean_ctor_set(x_378, 1, x_368);
return x_378;
}
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_7);
x_379 = lean_unsigned_to_nat(1u);
x_380 = lean_nat_add(x_13, x_379);
lean_dec(x_13);
x_381 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_381, 0, x_10);
lean_ctor_set(x_381, 1, x_11);
lean_ctor_set(x_381, 2, x_12);
lean_ctor_set(x_381, 3, x_380);
lean_ctor_set(x_381, 4, x_14);
lean_ctor_set(x_381, 5, x_15);
lean_ctor_set(x_381, 6, x_16);
lean_ctor_set(x_381, 7, x_17);
lean_ctor_set(x_381, 8, x_18);
lean_ctor_set(x_381, 9, x_19);
lean_ctor_set(x_381, 10, x_20);
x_382 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_381, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_ctor_get(x_1, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_1, 1);
lean_inc(x_385);
x_386 = 0;
lean_inc(x_384);
x_387 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_386, x_384, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_383);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_387, 1);
lean_inc(x_389);
lean_dec(x_387);
x_390 = lean_ctor_get(x_388, 3);
lean_inc(x_390);
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_391 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_390, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_389);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_box(0);
x_395 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_385, x_384, x_1, x_388, x_394, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_393);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_396 = lean_ctor_get(x_391, 1);
lean_inc(x_396);
lean_dec(x_391);
x_397 = lean_ctor_get(x_392, 0);
lean_inc(x_397);
lean_dec(x_392);
x_398 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_381, x_8, x_396);
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_388, x_397, x_5, x_6, x_381, x_8, x_399);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_box(0);
x_404 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_385, x_384, x_1, x_401, x_403, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_402);
return x_404;
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_388);
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_ctor_get(x_391, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_391, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_407 = x_391;
} else {
 lean_dec_ref(x_391);
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
case 1:
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_409 = lean_ctor_get(x_382, 1);
lean_inc(x_409);
lean_dec(x_382);
x_410 = lean_ctor_get(x_1, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_1, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_412, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_409);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_unbox(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
lean_dec(x_413);
lean_inc(x_1);
lean_inc(x_410);
x_417 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed), 14, 4);
lean_closure_set(x_417, 0, x_411);
lean_closure_set(x_417, 1, x_410);
lean_closure_set(x_417, 2, x_1);
lean_closure_set(x_417, 3, x_414);
x_418 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_box(0);
x_420 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_417, x_410, x_419, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_416);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; 
x_421 = lean_ctor_get(x_410, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_410, 2);
lean_inc(x_422);
x_423 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_421, x_422);
lean_dec(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_box(0);
x_425 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_417, x_410, x_424, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_416);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_431; 
x_426 = lean_st_ref_get(x_3, x_416);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get(x_427, 0);
lean_inc(x_429);
lean_dec(x_427);
x_430 = 0;
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
x_431 = l_Lean_Compiler_LCNF_normFunDeclImp(x_430, x_410, x_429, x_5, x_6, x_381, x_8, x_428);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
x_434 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_432, x_5, x_6, x_381, x_8, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
x_437 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_381, x_8, x_436);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
x_440 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_417, x_435, x_438, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_439);
lean_dec(x_438);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_417);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_441 = lean_ctor_get(x_434, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_434, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_443 = x_434;
} else {
 lean_dec_ref(x_434);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_417);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_445 = lean_ctor_get(x_431, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_431, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_447 = x_431;
} else {
 lean_dec_ref(x_431);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
}
}
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; 
x_449 = lean_ctor_get(x_413, 1);
lean_inc(x_449);
lean_dec(x_413);
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
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_410);
x_455 = l_Lean_Compiler_LCNF_normFunDeclImp(x_454, x_410, x_453, x_5, x_6, x_381, x_8, x_452);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
x_458 = lean_box(0);
x_459 = lean_unbox(x_414);
lean_dec(x_414);
x_460 = l_Lean_Compiler_LCNF_Simp_simp___lambda__3(x_411, x_410, x_1, x_459, x_456, x_458, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_457);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_414);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_461 = lean_ctor_get(x_455, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_455, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_463 = x_455;
} else {
 lean_dec_ref(x_455);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
}
}
case 2:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_465 = lean_ctor_get(x_382, 1);
lean_inc(x_465);
lean_dec(x_382);
x_466 = lean_ctor_get(x_1, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_1, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
x_469 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_468, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_465);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_unbox(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; uint8_t x_474; 
x_472 = lean_ctor_get(x_469, 1);
lean_inc(x_472);
lean_dec(x_469);
lean_inc(x_1);
lean_inc(x_466);
x_473 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed), 14, 4);
lean_closure_set(x_473, 0, x_467);
lean_closure_set(x_473, 1, x_466);
lean_closure_set(x_473, 2, x_1);
lean_closure_set(x_473, 3, x_470);
x_474 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_box(0);
x_476 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_473, x_466, x_475, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_472);
return x_476;
}
else
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
x_478 = lean_ctor_get(x_466, 2);
lean_inc(x_478);
x_479 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_477, x_478);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
x_480 = lean_box(0);
x_481 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_473, x_466, x_480, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_472);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; 
x_482 = lean_st_ref_get(x_3, x_472);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
lean_dec(x_483);
x_486 = 0;
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
x_487 = l_Lean_Compiler_LCNF_normFunDeclImp(x_486, x_466, x_485, x_5, x_6, x_381, x_8, x_484);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_487, 1);
lean_inc(x_489);
lean_dec(x_487);
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
x_490 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_488, x_5, x_6, x_381, x_8, x_489);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
x_493 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_381, x_8, x_492);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_473, x_491, x_494, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_495);
lean_dec(x_494);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_473);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_497 = lean_ctor_get(x_490, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_490, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_499 = x_490;
} else {
 lean_dec_ref(x_490);
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
lean_dec(x_473);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_501 = lean_ctor_get(x_487, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_487, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_503 = x_487;
} else {
 lean_dec_ref(x_487);
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
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; uint8_t x_510; lean_object* x_511; 
x_505 = lean_ctor_get(x_469, 1);
lean_inc(x_505);
lean_dec(x_469);
x_506 = lean_st_ref_get(x_3, x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_ctor_get(x_507, 0);
lean_inc(x_509);
lean_dec(x_507);
x_510 = 0;
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_466);
x_511 = l_Lean_Compiler_LCNF_normFunDeclImp(x_510, x_466, x_509, x_5, x_6, x_381, x_8, x_508);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_box(0);
x_515 = lean_unbox(x_470);
lean_dec(x_470);
x_516 = l_Lean_Compiler_LCNF_Simp_simp___lambda__6(x_467, x_466, x_1, x_515, x_512, x_514, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_513);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_470);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_517 = lean_ctor_get(x_511, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_511, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_519 = x_511;
} else {
 lean_dec_ref(x_511);
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
case 3:
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; uint8_t x_528; lean_object* x_529; 
x_521 = lean_ctor_get(x_382, 1);
lean_inc(x_521);
lean_dec(x_382);
x_522 = lean_ctor_get(x_1, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_1, 1);
lean_inc(x_523);
x_524 = lean_st_ref_get(x_3, x_521);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = lean_ctor_get(x_525, 0);
lean_inc(x_527);
lean_dec(x_525);
x_528 = 0;
lean_inc(x_522);
x_529 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_527, x_522, x_528);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_548; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
lean_dec(x_529);
lean_inc(x_523);
x_531 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_528, x_523, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_526);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_534 = x_531;
} else {
 lean_dec_ref(x_531);
 x_534 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_532);
lean_inc(x_530);
x_548 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_530, x_532, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_533);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; 
x_549 = lean_ctor_get(x_548, 0);
lean_inc(x_549);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; 
x_550 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
lean_dec(x_548);
lean_inc(x_530);
x_551 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_530, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_550);
x_552 = lean_ctor_get(x_551, 1);
lean_inc(x_552);
lean_dec(x_551);
x_553 = lean_array_get_size(x_532);
x_554 = lean_unsigned_to_nat(0u);
x_555 = lean_nat_dec_lt(x_554, x_553);
if (x_555 == 0)
{
lean_dec(x_553);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_535 = x_552;
goto block_547;
}
else
{
uint8_t x_556; 
x_556 = lean_nat_dec_le(x_553, x_553);
if (x_556 == 0)
{
lean_dec(x_553);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_535 = x_552;
goto block_547;
}
else
{
size_t x_557; size_t x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_557 = 0;
x_558 = lean_usize_of_nat(x_553);
lean_dec(x_553);
x_559 = lean_box(0);
x_560 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_532, x_557, x_558, x_559, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_552);
lean_dec(x_8);
lean_dec(x_381);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_535 = x_561;
goto block_547;
}
}
}
else
{
lean_object* x_562; lean_object* x_563; 
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_1);
x_562 = lean_ctor_get(x_548, 1);
lean_inc(x_562);
lean_dec(x_548);
x_563 = lean_ctor_get(x_549, 0);
lean_inc(x_563);
lean_dec(x_549);
x_1 = x_563;
x_7 = x_381;
x_9 = x_562;
goto _start;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_565 = lean_ctor_get(x_548, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_548, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_567 = x_548;
} else {
 lean_dec_ref(x_548);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
return x_568;
}
block_547:
{
uint8_t x_536; 
x_536 = lean_name_eq(x_522, x_530);
lean_dec(x_522);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_523);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_537 = x_1;
} else {
 lean_dec_ref(x_1);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(3, 2, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_530);
lean_ctor_set(x_538, 1, x_532);
if (lean_is_scalar(x_534)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_534;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_535);
return x_539;
}
else
{
size_t x_540; size_t x_541; uint8_t x_542; 
x_540 = lean_ptr_addr(x_523);
lean_dec(x_523);
x_541 = lean_ptr_addr(x_532);
x_542 = lean_usize_dec_eq(x_540, x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_543 = x_1;
} else {
 lean_dec_ref(x_1);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(3, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_530);
lean_ctor_set(x_544, 1, x_532);
if (lean_is_scalar(x_534)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_534;
}
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_535);
return x_545;
}
else
{
lean_object* x_546; 
lean_dec(x_532);
lean_dec(x_530);
if (lean_is_scalar(x_534)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_534;
}
lean_ctor_set(x_546, 0, x_1);
lean_ctor_set(x_546, 1, x_535);
return x_546;
}
}
}
}
else
{
lean_object* x_569; 
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_569 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_381, x_8, x_526);
lean_dec(x_8);
lean_dec(x_381);
lean_dec(x_6);
lean_dec(x_5);
return x_569;
}
}
case 4:
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_382, 1);
lean_inc(x_570);
lean_dec(x_382);
x_571 = lean_ctor_get(x_1, 0);
lean_inc(x_571);
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_571);
x_572 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_571, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_570);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; 
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_ctor_get(x_571, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_571, 1);
lean_inc(x_576);
x_577 = lean_ctor_get(x_571, 2);
lean_inc(x_577);
x_578 = lean_ctor_get(x_571, 3);
lean_inc(x_578);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 lean_ctor_release(x_571, 1);
 lean_ctor_release(x_571, 2);
 lean_ctor_release(x_571, 3);
 x_579 = x_571;
} else {
 lean_dec_ref(x_571);
 x_579 = lean_box(0);
}
x_580 = lean_st_ref_get(x_3, x_574);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_581, 0);
lean_inc(x_583);
lean_dec(x_581);
x_584 = 0;
lean_inc(x_577);
x_585 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_583, x_577, x_584);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
lean_dec(x_585);
x_587 = lean_st_ref_get(x_3, x_582);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = lean_ctor_get(x_588, 0);
lean_inc(x_590);
lean_dec(x_588);
lean_inc(x_576);
x_591 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_590, x_584, x_576);
lean_inc(x_586);
x_592 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_586, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_589);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
lean_dec(x_592);
lean_inc(x_586);
x_594 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7), 10, 1);
lean_closure_set(x_594, 0, x_586);
lean_inc(x_8);
lean_inc(x_381);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_578);
x_595 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_578, x_594, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_593);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_596, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_597);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; uint8_t x_634; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_601 = x_598;
} else {
 lean_dec_ref(x_598);
 x_601 = lean_box(0);
}
x_602 = lean_array_get_size(x_599);
x_634 = lean_nat_dec_eq(x_602, x_379);
if (x_634 == 0)
{
x_603 = x_584;
goto block_633;
}
else
{
lean_object* x_635; uint8_t x_636; 
x_635 = lean_unsigned_to_nat(0u);
x_636 = lean_nat_dec_lt(x_635, x_602);
if (x_636 == 0)
{
lean_object* x_637; lean_object* x_638; 
x_637 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_638 = l___private_Init_Util_0__outOfBounds___rarg(x_637);
if (lean_obj_tag(x_638) == 0)
{
lean_dec(x_638);
x_603 = x_584;
goto block_633;
}
else
{
uint8_t x_639; 
lean_dec(x_638);
x_639 = 1;
x_603 = x_639;
goto block_633;
}
}
else
{
lean_object* x_640; 
x_640 = lean_array_fget(x_599, x_635);
if (lean_obj_tag(x_640) == 0)
{
lean_dec(x_640);
x_603 = x_584;
goto block_633;
}
else
{
uint8_t x_641; 
lean_dec(x_640);
x_641 = 1;
x_603 = x_641;
goto block_633;
}
}
}
block_633:
{
if (x_603 == 0)
{
size_t x_604; size_t x_605; uint8_t x_606; 
lean_dec(x_602);
x_604 = lean_ptr_addr(x_578);
lean_dec(x_578);
x_605 = lean_ptr_addr(x_599);
x_606 = lean_usize_dec_eq(x_604, x_605);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_577);
lean_dec(x_576);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_607 = x_1;
} else {
 lean_dec_ref(x_1);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_608 = lean_alloc_ctor(0, 4, 0);
} else {
 x_608 = x_579;
}
lean_ctor_set(x_608, 0, x_575);
lean_ctor_set(x_608, 1, x_591);
lean_ctor_set(x_608, 2, x_586);
lean_ctor_set(x_608, 3, x_599);
if (lean_is_scalar(x_607)) {
 x_609 = lean_alloc_ctor(4, 1, 0);
} else {
 x_609 = x_607;
}
lean_ctor_set(x_609, 0, x_608);
if (lean_is_scalar(x_601)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_601;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_600);
return x_610;
}
else
{
size_t x_611; size_t x_612; uint8_t x_613; 
x_611 = lean_ptr_addr(x_576);
lean_dec(x_576);
x_612 = lean_ptr_addr(x_591);
x_613 = lean_usize_dec_eq(x_611, x_612);
if (x_613 == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_577);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_614 = x_1;
} else {
 lean_dec_ref(x_1);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_615 = lean_alloc_ctor(0, 4, 0);
} else {
 x_615 = x_579;
}
lean_ctor_set(x_615, 0, x_575);
lean_ctor_set(x_615, 1, x_591);
lean_ctor_set(x_615, 2, x_586);
lean_ctor_set(x_615, 3, x_599);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(4, 1, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_615);
if (lean_is_scalar(x_601)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_601;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_600);
return x_617;
}
else
{
uint8_t x_618; 
x_618 = lean_name_eq(x_577, x_586);
lean_dec(x_577);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_619 = x_1;
} else {
 lean_dec_ref(x_1);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_620 = lean_alloc_ctor(0, 4, 0);
} else {
 x_620 = x_579;
}
lean_ctor_set(x_620, 0, x_575);
lean_ctor_set(x_620, 1, x_591);
lean_ctor_set(x_620, 2, x_586);
lean_ctor_set(x_620, 3, x_599);
if (lean_is_scalar(x_619)) {
 x_621 = lean_alloc_ctor(4, 1, 0);
} else {
 x_621 = x_619;
}
lean_ctor_set(x_621, 0, x_620);
if (lean_is_scalar(x_601)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_601;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_600);
return x_622;
}
else
{
lean_object* x_623; 
lean_dec(x_599);
lean_dec(x_591);
lean_dec(x_586);
lean_dec(x_579);
lean_dec(x_575);
if (lean_is_scalar(x_601)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_601;
}
lean_ctor_set(x_623, 0, x_1);
lean_ctor_set(x_623, 1, x_600);
return x_623;
}
}
}
}
else
{
lean_object* x_624; uint8_t x_625; 
lean_dec(x_591);
lean_dec(x_586);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_1);
x_624 = lean_unsigned_to_nat(0u);
x_625 = lean_nat_dec_lt(x_624, x_602);
lean_dec(x_602);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_599);
x_626 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_627 = l___private_Init_Util_0__outOfBounds___rarg(x_626);
x_628 = l_Lean_Compiler_LCNF_AltCore_getCode(x_627);
lean_dec(x_627);
if (lean_is_scalar(x_601)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_601;
}
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_600);
return x_629;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_array_fget(x_599, x_624);
lean_dec(x_599);
x_631 = l_Lean_Compiler_LCNF_AltCore_getCode(x_630);
lean_dec(x_630);
if (lean_is_scalar(x_601)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_601;
}
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_600);
return x_632;
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_591);
lean_dec(x_586);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_1);
x_642 = lean_ctor_get(x_598, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_598, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_644 = x_598;
} else {
 lean_dec_ref(x_598);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_591);
lean_dec(x_586);
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_646 = lean_ctor_get(x_595, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_595, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_595)) {
 lean_ctor_release(x_595, 0);
 lean_ctor_release(x_595, 1);
 x_648 = x_595;
} else {
 lean_dec_ref(x_595);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; 
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_650 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_381, x_8, x_582);
lean_dec(x_8);
lean_dec(x_381);
lean_dec(x_6);
lean_dec(x_5);
return x_650;
}
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
lean_dec(x_571);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_651 = lean_ctor_get(x_572, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_652 = x_572;
} else {
 lean_dec_ref(x_572);
 x_652 = lean_box(0);
}
x_653 = lean_ctor_get(x_573, 0);
lean_inc(x_653);
lean_dec(x_573);
if (lean_is_scalar(x_652)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_652;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_651);
return x_654;
}
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
lean_dec(x_571);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_655 = lean_ctor_get(x_572, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_572, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_572)) {
 lean_ctor_release(x_572, 0);
 lean_ctor_release(x_572, 1);
 x_657 = x_572;
} else {
 lean_dec_ref(x_572);
 x_657 = lean_box(0);
}
if (lean_is_scalar(x_657)) {
 x_658 = lean_alloc_ctor(1, 2, 0);
} else {
 x_658 = x_657;
}
lean_ctor_set(x_658, 0, x_655);
lean_ctor_set(x_658, 1, x_656);
return x_658;
}
}
case 5:
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; 
x_659 = lean_ctor_get(x_382, 1);
lean_inc(x_659);
lean_dec(x_382);
x_660 = lean_ctor_get(x_1, 0);
lean_inc(x_660);
x_661 = lean_st_ref_get(x_3, x_659);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_ctor_get(x_662, 0);
lean_inc(x_664);
lean_dec(x_662);
x_665 = 0;
lean_inc(x_660);
x_666 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_664, x_660, x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; uint8_t x_671; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
lean_dec(x_666);
lean_inc(x_667);
x_668 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_667, x_2, x_3, x_4, x_5, x_6, x_381, x_8, x_663);
lean_dec(x_8);
lean_dec(x_381);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_670 = x_668;
} else {
 lean_dec_ref(x_668);
 x_670 = lean_box(0);
}
x_671 = lean_name_eq(x_660, x_667);
lean_dec(x_660);
if (x_671 == 0)
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_672 = x_1;
} else {
 lean_dec_ref(x_1);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(5, 1, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_667);
if (lean_is_scalar(x_670)) {
 x_674 = lean_alloc_ctor(0, 2, 0);
} else {
 x_674 = x_670;
}
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_669);
return x_674;
}
else
{
lean_object* x_675; 
lean_dec(x_667);
if (lean_is_scalar(x_670)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_670;
}
lean_ctor_set(x_675, 0, x_1);
lean_ctor_set(x_675, 1, x_669);
return x_675;
}
}
else
{
lean_object* x_676; 
lean_dec(x_660);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_676 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_381, x_8, x_663);
lean_dec(x_8);
lean_dec(x_381);
lean_dec(x_6);
lean_dec(x_5);
return x_676;
}
}
default: 
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; size_t x_686; size_t x_687; uint8_t x_688; 
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_677 = lean_ctor_get(x_382, 1);
lean_inc(x_677);
lean_dec(x_382);
x_678 = lean_ctor_get(x_1, 0);
lean_inc(x_678);
x_679 = lean_st_ref_get(x_3, x_677);
lean_dec(x_3);
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
x_683 = lean_ctor_get(x_680, 0);
lean_inc(x_683);
lean_dec(x_680);
x_684 = 0;
lean_inc(x_678);
x_685 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_683, x_684, x_678);
x_686 = lean_ptr_addr(x_678);
lean_dec(x_678);
x_687 = lean_ptr_addr(x_685);
x_688 = lean_usize_dec_eq(x_686, x_687);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_689 = x_1;
} else {
 lean_dec_ref(x_1);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(6, 1, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_685);
if (lean_is_scalar(x_682)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_682;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_681);
return x_691;
}
else
{
lean_object* x_692; 
lean_dec(x_685);
if (lean_is_scalar(x_682)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_682;
}
lean_ctor_set(x_692, 0, x_1);
lean_ctor_set(x_692, 1, x_681);
return x_692;
}
}
}
}
}
else
{
lean_object* x_693; 
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
x_693 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_693;
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
