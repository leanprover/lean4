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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
lean_object* l_outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1754_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_betaReduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_15 = l_outOfBounds___rarg(x_14);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
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
x_21 = l_Lean_Compiler_LCNF_replaceExprFVars(x_19, x_18, x_20, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 0;
x_25 = l_Lean_Compiler_LCNF_mkAuxParam(x_22, x_24, x_8, x_9, x_10, x_11, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_29 = lean_array_push(x_17, x_27);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_Expr_fvar___override(x_31);
x_33 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_30, x_32);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_29);
x_34 = 1;
x_35 = lean_usize_add(x_3, x_34);
x_3 = x_35;
x_4 = x_25;
x_12 = x_28;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
lean_inc(x_37);
x_39 = lean_array_push(x_17, x_37);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lean_Expr_fvar___override(x_41);
x_43 = l_Lean_HashMap_insert___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_18, x_40, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
x_4 = x_44;
x_12 = x_38;
goto _start;
}
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
x_1 = lean_mk_string_unchecked("_f", 2, 2);
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
lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_20);
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
return x_32;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
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
lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 0);
if (x_11 == 0)
{
lean_object* x_214; 
x_214 = lean_box(0);
x_12 = x_214;
x_13 = x_9;
goto block_213;
}
else
{
lean_object* x_215; 
x_215 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_12 = x_215;
x_13 = x_9;
goto block_213;
}
block_213:
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
uint8_t x_209; 
x_209 = 0;
x_32 = x_209;
goto block_208;
}
else
{
uint8_t x_210; 
x_210 = 1;
x_32 = x_210;
goto block_208;
}
block_208:
{
lean_object* x_33; lean_object* x_34; 
if (x_32 == 0)
{
lean_object* x_206; 
x_206 = lean_box(0);
x_33 = x_206;
x_34 = x_23;
goto block_205;
}
else
{
lean_object* x_207; 
x_207 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_33 = x_207;
x_34 = x_23;
goto block_205;
}
block_205:
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_202; 
lean_dec(x_33);
lean_dec(x_24);
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
x_202 = lean_unbox(x_38);
lean_dec(x_38);
if (x_202 == 0)
{
uint8_t x_203; 
x_203 = 1;
x_41 = x_203;
goto block_201;
}
else
{
uint8_t x_204; 
x_204 = 0;
x_41 = x_204;
goto block_201;
}
block_201:
{
uint8_t x_42; 
if (x_41 == 0)
{
uint8_t x_199; 
x_199 = 0;
x_42 = x_199;
goto block_198;
}
else
{
uint8_t x_200; 
x_200 = 1;
x_42 = x_200;
goto block_198;
}
block_198:
{
lean_object* x_43; lean_object* x_44; 
if (x_42 == 0)
{
lean_object* x_196; 
x_196 = lean_box(0);
x_43 = x_196;
x_44 = x_39;
goto block_195;
}
else
{
lean_object* x_197; 
x_197 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_43 = x_197;
x_44 = x_39;
goto block_195;
}
block_195:
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
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
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_19);
x_60 = l_Lean_Compiler_LCNF_Decl_getArity(x_57);
lean_dec(x_57);
x_61 = lean_nat_dec_lt(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_193; 
x_193 = lean_box(0);
x_62 = x_193;
x_63 = x_55;
goto block_192;
}
else
{
lean_object* x_194; 
x_194 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_62 = x_194;
x_63 = x_55;
goto block_192;
}
block_192:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_64 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_56;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_56);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 2);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_mkNewParams(x_68, x_5, x_6, x_7, x_8, x_63);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_array_get_size(x_71);
x_74 = lean_usize_of_nat(x_73);
lean_dec(x_73);
x_75 = 0;
lean_inc(x_71);
x_76 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_74, x_75, x_71);
x_77 = l_Array_append___rarg(x_19, x_76);
lean_dec(x_76);
if (lean_is_scalar(x_20)) {
 x_78 = lean_alloc_ctor(3, 3, 0);
} else {
 x_78 = x_20;
}
lean_ctor_set(x_78, 0, x_17);
lean_ctor_set(x_78, 1, x_18);
lean_ctor_set(x_78, 2, x_77);
x_79 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_80 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_78, x_79, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_scalar(x_58)) {
 x_84 = lean_alloc_ctor(5, 1, 0);
} else {
 x_84 = x_58;
 lean_ctor_set_tag(x_84, 5);
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_69, 1, x_84);
lean_ctor_set(x_69, 0, x_81);
x_85 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_86 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_71, x_69, x_85, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_89, x_90, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
lean_ctor_set(x_62, 0, x_87);
lean_ctor_set(x_93, 0, x_62);
return x_93;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
lean_ctor_set(x_62, 0, x_87);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_62);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_dec(x_87);
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_91);
if (x_98 == 0)
{
return x_91;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_91, 0);
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_91);
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
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_86);
if (x_102 == 0)
{
return x_86;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_86, 0);
x_104 = lean_ctor_get(x_86, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_86);
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
lean_free_object(x_69);
lean_dec(x_71);
lean_free_object(x_62);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_80);
if (x_106 == 0)
{
return x_80;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_80, 0);
x_108 = lean_ctor_get(x_80, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_80);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_69, 0);
x_111 = lean_ctor_get(x_69, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_69);
x_112 = lean_array_get_size(x_110);
x_113 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_114 = 0;
lean_inc(x_110);
x_115 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_113, x_114, x_110);
x_116 = l_Array_append___rarg(x_19, x_115);
lean_dec(x_115);
if (lean_is_scalar(x_20)) {
 x_117 = lean_alloc_ctor(3, 3, 0);
} else {
 x_117 = x_20;
}
lean_ctor_set(x_117, 0, x_17);
lean_ctor_set(x_117, 1, x_18);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_119 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_117, x_118, x_5, x_6, x_7, x_8, x_111);
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
if (lean_is_scalar(x_58)) {
 x_123 = lean_alloc_ctor(5, 1, 0);
} else {
 x_123 = x_58;
 lean_ctor_set_tag(x_123, 5);
}
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_110, x_124, x_125, x_5, x_6, x_7, x_8, x_121);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_1, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_129, x_130, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
lean_ctor_set(x_62, 0, x_127);
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_62);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_127);
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_137 = lean_ctor_get(x_131, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_141 = lean_ctor_get(x_126, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_126, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_143 = x_126;
} else {
 lean_dec_ref(x_126);
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
lean_dec(x_110);
lean_free_object(x_62);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_145 = lean_ctor_get(x_119, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_147 = x_119;
} else {
 lean_dec_ref(x_119);
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
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_62);
x_149 = lean_ctor_get(x_1, 2);
lean_inc(x_149);
x_150 = l_Lean_Compiler_LCNF_mkNewParams(x_149, x_5, x_6, x_7, x_8, x_63);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_array_get_size(x_151);
x_155 = lean_usize_of_nat(x_154);
lean_dec(x_154);
x_156 = 0;
lean_inc(x_151);
x_157 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_155, x_156, x_151);
x_158 = l_Array_append___rarg(x_19, x_157);
lean_dec(x_157);
if (lean_is_scalar(x_20)) {
 x_159 = lean_alloc_ctor(3, 3, 0);
} else {
 x_159 = x_20;
}
lean_ctor_set(x_159, 0, x_17);
lean_ctor_set(x_159, 1, x_18);
lean_ctor_set(x_159, 2, x_158);
x_160 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_161 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_159, x_160, x_5, x_6, x_7, x_8, x_152);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
if (lean_is_scalar(x_58)) {
 x_165 = lean_alloc_ctor(5, 1, 0);
} else {
 x_165 = x_58;
 lean_ctor_set_tag(x_165, 5);
}
lean_ctor_set(x_165, 0, x_164);
if (lean_is_scalar(x_153)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_153;
}
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_168 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_151, x_166, x_167, x_5, x_6, x_7, x_8, x_163);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_1, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_171, x_172, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_170);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_174);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_177 = x_175;
} else {
 lean_dec_ref(x_175);
 x_177 = lean_box(0);
}
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_169);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_169);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_173, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_182 = x_173;
} else {
 lean_dec_ref(x_173);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_184 = lean_ctor_get(x_168, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_168, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_186 = x_168;
} else {
 lean_dec_ref(x_168);
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
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_188 = lean_ctor_get(x_161, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_161, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_190 = x_161;
} else {
 lean_dec_ref(x_161);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
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
lean_object* x_211; lean_object* x_212; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_211 = lean_box(0);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_13);
return x_212;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
case 4:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
case 5:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_st_ref_get(x_4, x_10);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
x_28 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_26, x_22, x_27);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_name_eq(x_29, x_2);
lean_dec(x_29);
x_31 = lean_box(x_30);
lean_ctor_set(x_23, 0, x_31);
return x_23;
}
else
{
lean_object* x_32; 
x_32 = lean_box(x_27);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 0;
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_35, x_22, x_36);
lean_dec(x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_name_eq(x_38, x_2);
lean_dec(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
}
}
case 6:
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_44 = 0;
x_45 = lean_box(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
default: 
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_1, 1);
lean_dec(x_48);
x_49 = lean_ctor_get(x_1, 0);
lean_dec(x_49);
x_50 = 0;
x_51 = lean_box(x_50);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_51);
return x_1;
}
else
{
uint8_t x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_10);
return x_54;
}
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
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
lean_ctor_set(x_28, 1, x_9);
return x_28;
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc(x_9);
x_15 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_9, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_nat_dec_lt(x_4, x_5);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_15);
lean_dec(x_8);
lean_dec(x_4);
x_20 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_9, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_Simp_simp(x_7, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_array_get_size(x_8);
x_28 = l_Array_toSubarray___rarg(x_8, x_4, x_27);
x_29 = l_Array_ofSubarray___rarg(x_28);
lean_dec(x_28);
lean_ctor_set_tag(x_15, 4);
lean_ctor_set(x_15, 1, x_29);
lean_ctor_set(x_15, 0, x_9);
x_30 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_15, x_30, x_10, x_11, x_12, x_13, x_17);
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
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_dec(x_15);
x_48 = lean_nat_dec_lt(x_4, x_5);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_4);
x_49 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_9, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = l_Lean_Compiler_LCNF_Simp_simp(x_7, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_54 = x_49;
} else {
 lean_dec_ref(x_49);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_array_get_size(x_8);
x_57 = l_Array_toSubarray___rarg(x_8, x_4, x_56);
x_58 = l_Array_ofSubarray___rarg(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_9);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_61 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_59, x_60, x_10, x_11, x_12, x_13, x_47);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_6, x_64, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_7);
x_68 = l_Lean_Compiler_LCNF_Simp_simp(x_67, x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_61, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_61, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_75 = x_61;
} else {
 lean_dec_ref(x_61);
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
x_1 = lean_mk_string_unchecked("_jp", 3, 3);
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_32);
switch (lean_obj_tag(x_11)) {
case 0:
{
uint8_t x_34; lean_object* x_35; 
lean_dec(x_11);
x_34 = 0;
lean_inc(x_33);
x_35 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_508; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_508 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_508 == 0)
{
lean_object* x_509; 
x_509 = lean_box(0);
x_38 = x_509;
goto block_507;
}
else
{
uint8_t x_510; 
x_510 = lean_nat_dec_eq(x_24, x_27);
if (x_510 == 0)
{
lean_object* x_511; 
x_511 = lean_box(0);
x_38 = x_511;
goto block_507;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_512 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
lean_dec(x_512);
x_514 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_513);
if (lean_obj_tag(x_514) == 0)
{
uint8_t x_515; 
x_515 = !lean_is_exclusive(x_514);
if (x_515 == 0)
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_514, 0);
x_517 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_514, 0, x_517);
return x_514;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_518 = lean_ctor_get(x_514, 0);
x_519 = lean_ctor_get(x_514, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_514);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_518);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_519);
return x_521;
}
}
else
{
uint8_t x_522; 
x_522 = !lean_is_exclusive(x_514);
if (x_522 == 0)
{
return x_514;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_514, 0);
x_524 = lean_ctor_get(x_514, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_514);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
}
block_507:
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
lean_object* x_43; uint8_t x_44; 
x_43 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_21, 2);
lean_inc(x_47);
lean_dec(x_21);
x_48 = l_Lean_Compiler_LCNF_inferAppType(x_47, x_33, x_6, x_7, x_8, x_9, x_45);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_52 = l_Lean_Expr_headBeta(x_50);
x_53 = l_Lean_Expr_isForall(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_54 = l_Lean_Compiler_LCNF_mkAuxParam(x_50, x_34, x_6, x_7, x_8, x_9, x_51);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_59 == 0)
{
lean_object* x_88; 
lean_free_object(x_48);
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_88 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_90 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_60 = x_91;
x_61 = x_92;
goto block_87;
}
else
{
uint8_t x_93; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_90);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_57);
lean_dec(x_55);
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
x_97 = !lean_is_exclusive(x_88);
if (x_97 == 0)
{
return x_88;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_88, 0);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_88);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_array_get_size(x_23);
x_102 = l_Array_toSubarray___rarg(x_23, x_27, x_101);
x_103 = l_Array_ofSubarray___rarg(x_102);
lean_dec(x_102);
lean_ctor_set_tag(x_48, 4);
lean_ctor_set(x_48, 1, x_103);
lean_ctor_set(x_48, 0, x_58);
x_104 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_105 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_48, x_104, x_6, x_7, x_8, x_9, x_56);
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
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 0, x_106);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_111 = l_Lean_Compiler_LCNF_Simp_simp(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_60 = x_112;
x_61 = x_113;
goto block_87;
}
else
{
uint8_t x_114; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_114 = !lean_is_exclusive(x_111);
if (x_114 == 0)
{
return x_111;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_111, 0);
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_111);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_106);
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_43);
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
x_118 = !lean_is_exclusive(x_109);
if (x_118 == 0)
{
return x_109;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_109, 0);
x_120 = lean_ctor_get(x_109, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_109);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_57);
lean_dec(x_55);
lean_free_object(x_43);
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
x_122 = !lean_is_exclusive(x_105);
if (x_122 == 0)
{
return x_105;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_105, 0);
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_105);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_87:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_63 = lean_array_push(x_62, x_55);
x_64 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_65 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_63, x_60, x_64, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_62);
x_69 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_68, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_is_scalar(x_57)) {
 x_72 = lean_alloc_ctor(2, 2, 0);
} else {
 x_72 = x_57;
 lean_ctor_set_tag(x_72, 2);
}
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
if (lean_is_scalar(x_22)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_22;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
if (lean_is_scalar(x_57)) {
 x_76 = lean_alloc_ctor(2, 2, 0);
} else {
 x_76 = x_57;
 lean_ctor_set_tag(x_76, 2);
}
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_74);
if (lean_is_scalar(x_22)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_22;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_66);
lean_dec(x_57);
lean_dec(x_22);
x_79 = !lean_is_exclusive(x_69);
if (x_79 == 0)
{
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
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
lean_dec(x_57);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_50);
x_126 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_127 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_128 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_126, x_40, x_127, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_131 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_129, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_135 == 0)
{
lean_object* x_150; 
lean_free_object(x_48);
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_150 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_133);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_152 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_136 = x_153;
x_137 = x_154;
goto block_149;
}
else
{
uint8_t x_155; 
lean_dec(x_132);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_155 = !lean_is_exclusive(x_152);
if (x_155 == 0)
{
return x_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_152, 0);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_152);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_132);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_150);
if (x_159 == 0)
{
return x_150;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_150, 0);
x_161 = lean_ctor_get(x_150, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_150);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_array_get_size(x_23);
x_164 = l_Array_toSubarray___rarg(x_23, x_27, x_163);
x_165 = l_Array_ofSubarray___rarg(x_164);
lean_dec(x_164);
lean_ctor_set_tag(x_48, 4);
lean_ctor_set(x_48, 1, x_165);
lean_ctor_set(x_48, 0, x_134);
x_166 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_167 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_48, x_166, x_6, x_7, x_8, x_9, x_133);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 0, x_168);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_173 = l_Lean_Compiler_LCNF_Simp_simp(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_136 = x_174;
x_137 = x_175;
goto block_149;
}
else
{
uint8_t x_176; 
lean_dec(x_132);
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
lean_dec(x_168);
lean_dec(x_132);
lean_free_object(x_43);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_171);
if (x_180 == 0)
{
return x_171;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_171, 0);
x_182 = lean_ctor_get(x_171, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_171);
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
lean_dec(x_132);
lean_free_object(x_43);
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
x_184 = !lean_is_exclusive(x_167);
if (x_184 == 0)
{
return x_167;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_167, 0);
x_186 = lean_ctor_get(x_167, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_167);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
block_149:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_132);
x_139 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_140 = lean_array_push(x_139, x_138);
x_141 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_140, x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_137);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_140);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
if (lean_is_scalar(x_22)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_22;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_141);
if (lean_is_scalar(x_22)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_22;
}
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
uint8_t x_188; 
lean_free_object(x_48);
lean_free_object(x_43);
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
x_188 = !lean_is_exclusive(x_131);
if (x_188 == 0)
{
return x_131;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_131, 0);
x_190 = lean_ctor_get(x_131, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_131);
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
lean_free_object(x_48);
lean_free_object(x_43);
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
x_192 = !lean_is_exclusive(x_128);
if (x_192 == 0)
{
return x_128;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_128, 0);
x_194 = lean_ctor_get(x_128, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_128);
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
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_48, 0);
x_197 = lean_ctor_get(x_48, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_48);
lean_inc(x_196);
x_198 = l_Lean_Expr_headBeta(x_196);
x_199 = l_Lean_Expr_isForall(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_200 = l_Lean_Compiler_LCNF_mkAuxParam(x_196, x_34, x_6, x_7, x_8, x_9, x_197);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
x_205 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_205 == 0)
{
lean_object* x_231; 
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_231 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_204, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_202);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_233 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_206 = x_234;
x_207 = x_235;
goto block_230;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
}
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_203);
lean_dec(x_201);
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
x_240 = lean_ctor_get(x_231, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_231, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_242 = x_231;
} else {
 lean_dec_ref(x_231);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_array_get_size(x_23);
x_245 = l_Array_toSubarray___rarg(x_23, x_27, x_244);
x_246 = l_Array_ofSubarray___rarg(x_245);
lean_dec(x_245);
x_247 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_247, 0, x_204);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_249 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_247, x_248, x_6, x_7, x_8, x_9, x_202);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_252, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 0, x_250);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_255 = l_Lean_Compiler_LCNF_Simp_simp(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_206 = x_256;
x_207 = x_257;
goto block_230;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_203);
lean_dec(x_201);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_258 = lean_ctor_get(x_255, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_260 = x_255;
} else {
 lean_dec_ref(x_255);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_250);
lean_dec(x_203);
lean_dec(x_201);
lean_free_object(x_43);
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
x_262 = lean_ctor_get(x_253, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_253, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_264 = x_253;
} else {
 lean_dec_ref(x_253);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_203);
lean_dec(x_201);
lean_free_object(x_43);
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
x_266 = lean_ctor_get(x_249, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_249, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_268 = x_249;
} else {
 lean_dec_ref(x_249);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
block_230:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_209 = lean_array_push(x_208, x_201);
x_210 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_211 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_209, x_206, x_210, x_6, x_7, x_8, x_9, x_207);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_212);
x_214 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_214, 0, x_212);
lean_closure_set(x_214, 1, x_208);
x_215 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_214, x_6, x_7, x_8, x_9, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_219 = lean_alloc_ctor(2, 2, 0);
} else {
 x_219 = x_203;
 lean_ctor_set_tag(x_219, 2);
}
lean_ctor_set(x_219, 0, x_212);
lean_ctor_set(x_219, 1, x_216);
if (lean_is_scalar(x_22)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_22;
}
lean_ctor_set(x_220, 0, x_219);
if (lean_is_scalar(x_218)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_218;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_217);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_212);
lean_dec(x_203);
lean_dec(x_22);
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_215, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_224 = x_215;
} else {
 lean_dec_ref(x_215);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_203);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_226 = lean_ctor_get(x_211, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_211, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_228 = x_211;
} else {
 lean_dec_ref(x_211);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_196);
x_270 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_271 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_272 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_270, x_40, x_271, x_6, x_7, x_8, x_9, x_197);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_275 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_273, x_6, x_7, x_8, x_9, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; lean_object* x_281; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
x_279 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_279 == 0)
{
lean_object* x_292; 
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_292 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_278, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_277);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_294 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_280 = x_295;
x_281 = x_296;
goto block_291;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_276);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_294, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_299 = x_294;
} else {
 lean_dec_ref(x_294);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_276);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_301 = lean_ctor_get(x_292, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_292, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_303 = x_292;
} else {
 lean_dec_ref(x_292);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_305 = lean_array_get_size(x_23);
x_306 = l_Array_toSubarray___rarg(x_23, x_27, x_305);
x_307 = l_Array_ofSubarray___rarg(x_306);
lean_dec(x_306);
x_308 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_308, 0, x_278);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_310 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_308, x_309, x_6, x_7, x_8, x_9, x_277);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_ctor_get(x_311, 0);
lean_inc(x_313);
x_314 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_313, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_312);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
lean_ctor_set(x_43, 1, x_2);
lean_ctor_set(x_43, 0, x_311);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_316 = l_Lean_Compiler_LCNF_Simp_simp(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_280 = x_317;
x_281 = x_318;
goto block_291;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_276);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_319 = lean_ctor_get(x_316, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_316, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_321 = x_316;
} else {
 lean_dec_ref(x_316);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_311);
lean_dec(x_276);
lean_free_object(x_43);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_323 = lean_ctor_get(x_314, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_314, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_325 = x_314;
} else {
 lean_dec_ref(x_314);
 x_325 = lean_box(0);
}
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_323);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_276);
lean_free_object(x_43);
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
x_327 = lean_ctor_get(x_310, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_310, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_329 = x_310;
} else {
 lean_dec_ref(x_310);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
}
block_291:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_276);
x_283 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_284 = lean_array_push(x_283, x_282);
x_285 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_284, x_280, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_281);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_289 = lean_alloc_ctor(1, 1, 0);
} else {
 x_289 = x_22;
}
lean_ctor_set(x_289, 0, x_286);
if (lean_is_scalar(x_288)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_288;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_287);
return x_290;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_free_object(x_43);
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
x_331 = lean_ctor_get(x_275, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_275, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_333 = x_275;
} else {
 lean_dec_ref(x_275);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_free_object(x_43);
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
x_335 = lean_ctor_get(x_272, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_272, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_337 = x_272;
} else {
 lean_dec_ref(x_272);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_339 = lean_ctor_get(x_43, 1);
lean_inc(x_339);
lean_dec(x_43);
x_340 = lean_ctor_get(x_21, 2);
lean_inc(x_340);
lean_dec(x_21);
x_341 = l_Lean_Compiler_LCNF_inferAppType(x_340, x_33, x_6, x_7, x_8, x_9, x_339);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
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
lean_inc(x_342);
x_345 = l_Lean_Expr_headBeta(x_342);
x_346 = l_Lean_Expr_isForall(x_345);
lean_dec(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; 
x_347 = l_Lean_Compiler_LCNF_mkAuxParam(x_342, x_34, x_6, x_7, x_8, x_9, x_343);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_348, 0);
lean_inc(x_351);
x_352 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_352 == 0)
{
lean_object* x_378; 
lean_dec(x_344);
lean_dec(x_27);
lean_dec(x_23);
x_378 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_351, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_349);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_380 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_353 = x_381;
x_354 = x_382;
goto block_377;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_383 = lean_ctor_get(x_380, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_385 = x_380;
} else {
 lean_dec_ref(x_380);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_350);
lean_dec(x_348);
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
x_387 = lean_ctor_get(x_378, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_378, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_389 = x_378;
} else {
 lean_dec_ref(x_378);
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
x_391 = lean_array_get_size(x_23);
x_392 = l_Array_toSubarray___rarg(x_23, x_27, x_391);
x_393 = l_Array_ofSubarray___rarg(x_392);
lean_dec(x_392);
if (lean_is_scalar(x_344)) {
 x_394 = lean_alloc_ctor(4, 2, 0);
} else {
 x_394 = x_344;
 lean_ctor_set_tag(x_394, 4);
}
lean_ctor_set(x_394, 0, x_351);
lean_ctor_set(x_394, 1, x_393);
x_395 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_396 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_394, x_395, x_6, x_7, x_8, x_9, x_349);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_399, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_398);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
lean_dec(x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_397);
lean_ctor_set(x_402, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_403 = l_Lean_Compiler_LCNF_Simp_simp(x_402, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_401);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
x_353 = x_404;
x_354 = x_405;
goto block_377;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_408 = x_403;
} else {
 lean_dec_ref(x_403);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_406);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_397);
lean_dec(x_350);
lean_dec(x_348);
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
x_410 = lean_ctor_get(x_400, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_400, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_412 = x_400;
} else {
 lean_dec_ref(x_400);
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
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_350);
lean_dec(x_348);
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
x_414 = lean_ctor_get(x_396, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_396, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_416 = x_396;
} else {
 lean_dec_ref(x_396);
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
block_377:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_356 = lean_array_push(x_355, x_348);
x_357 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_358 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_356, x_353, x_357, x_6, x_7, x_8, x_9, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_359);
x_361 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_361, 0, x_359);
lean_closure_set(x_361, 1, x_355);
x_362 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_361, x_6, x_7, x_8, x_9, x_360);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_365 = x_362;
} else {
 lean_dec_ref(x_362);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_366 = lean_alloc_ctor(2, 2, 0);
} else {
 x_366 = x_350;
 lean_ctor_set_tag(x_366, 2);
}
lean_ctor_set(x_366, 0, x_359);
lean_ctor_set(x_366, 1, x_363);
if (lean_is_scalar(x_22)) {
 x_367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_367 = x_22;
}
lean_ctor_set(x_367, 0, x_366);
if (lean_is_scalar(x_365)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_365;
}
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_364);
return x_368;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_359);
lean_dec(x_350);
lean_dec(x_22);
x_369 = lean_ctor_get(x_362, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_362, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_371 = x_362;
} else {
 lean_dec_ref(x_362);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec(x_350);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_373 = lean_ctor_get(x_358, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_358, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_375 = x_358;
} else {
 lean_dec_ref(x_358);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_342);
x_418 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_419 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_420 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_418, x_40, x_419, x_6, x_7, x_8, x_9, x_343);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_423 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_421, x_6, x_7, x_8, x_9, x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
x_427 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_427 == 0)
{
lean_object* x_440; 
lean_dec(x_344);
lean_dec(x_27);
lean_dec(x_23);
x_440 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_426, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_425);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec(x_440);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_442 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_428 = x_443;
x_429 = x_444;
goto block_439;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_424);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_445 = lean_ctor_get(x_442, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_442, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_447 = x_442;
} else {
 lean_dec_ref(x_442);
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
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_424);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_449 = lean_ctor_get(x_440, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_440, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_451 = x_440;
} else {
 lean_dec_ref(x_440);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_453 = lean_array_get_size(x_23);
x_454 = l_Array_toSubarray___rarg(x_23, x_27, x_453);
x_455 = l_Array_ofSubarray___rarg(x_454);
lean_dec(x_454);
if (lean_is_scalar(x_344)) {
 x_456 = lean_alloc_ctor(4, 2, 0);
} else {
 x_456 = x_344;
 lean_ctor_set_tag(x_456, 4);
}
lean_ctor_set(x_456, 0, x_426);
lean_ctor_set(x_456, 1, x_455);
x_457 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_458 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_456, x_457, x_6, x_7, x_8, x_9, x_425);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 0);
lean_inc(x_461);
x_462 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_461, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_460);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
lean_dec(x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_459);
lean_ctor_set(x_464, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_465 = l_Lean_Compiler_LCNF_Simp_simp(x_464, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_428 = x_466;
x_429 = x_467;
goto block_439;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_424);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_468 = lean_ctor_get(x_465, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_470 = x_465;
} else {
 lean_dec_ref(x_465);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_459);
lean_dec(x_424);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_472 = lean_ctor_get(x_462, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_462, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_474 = x_462;
} else {
 lean_dec_ref(x_462);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_424);
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
x_476 = lean_ctor_get(x_458, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_458, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_478 = x_458;
} else {
 lean_dec_ref(x_458);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
block_439:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_424);
x_431 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_432 = lean_array_push(x_431, x_430);
x_433 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_432, x_428, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_429);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_432);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_436 = x_433;
} else {
 lean_dec_ref(x_433);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_22;
}
lean_ctor_set(x_437, 0, x_434);
if (lean_is_scalar(x_436)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_436;
}
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_435);
return x_438;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_344);
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
x_480 = lean_ctor_get(x_423, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_423, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_482 = x_423;
} else {
 lean_dec_ref(x_423);
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
lean_dec(x_344);
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
x_484 = lean_ctor_get(x_420, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_420, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_486 = x_420;
} else {
 lean_dec_ref(x_420);
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
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_33);
lean_dec(x_21);
x_488 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
x_490 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_490, 0, x_3);
lean_closure_set(x_490, 1, x_4);
lean_closure_set(x_490, 2, x_5);
lean_closure_set(x_490, 3, x_27);
lean_closure_set(x_490, 4, x_24);
lean_closure_set(x_490, 5, x_26);
lean_closure_set(x_490, 6, x_2);
lean_closure_set(x_490, 7, x_23);
x_491 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_490, x_6, x_7, x_8, x_9, x_489);
if (lean_obj_tag(x_491) == 0)
{
uint8_t x_492; 
x_492 = !lean_is_exclusive(x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_491, 0);
if (lean_is_scalar(x_22)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_22;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_491, 0, x_494);
return x_491;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_495 = lean_ctor_get(x_491, 0);
x_496 = lean_ctor_get(x_491, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_491);
if (lean_is_scalar(x_22)) {
 x_497 = lean_alloc_ctor(1, 1, 0);
} else {
 x_497 = x_22;
}
lean_ctor_set(x_497, 0, x_495);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
else
{
uint8_t x_499; 
lean_dec(x_22);
x_499 = !lean_is_exclusive(x_491);
if (x_499 == 0)
{
return x_491;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_491, 0);
x_501 = lean_ctor_get(x_491, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_491);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
}
else
{
uint8_t x_503; 
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
x_503 = !lean_is_exclusive(x_39);
if (x_503 == 0)
{
return x_39;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_39, 0);
x_505 = lean_ctor_get(x_39, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_39);
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
uint8_t x_526; 
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
x_526 = !lean_is_exclusive(x_35);
if (x_526 == 0)
{
return x_35;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_35, 0);
x_528 = lean_ctor_get(x_35, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_35);
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_527);
lean_ctor_set(x_529, 1, x_528);
return x_529;
}
}
}
case 1:
{
uint8_t x_530; lean_object* x_531; 
x_530 = 0;
lean_inc(x_33);
x_531 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_530, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_1004; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
lean_dec(x_531);
x_1004 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1004 == 0)
{
lean_object* x_1005; 
x_1005 = lean_box(0);
x_534 = x_1005;
goto block_1003;
}
else
{
uint8_t x_1006; 
x_1006 = lean_nat_dec_eq(x_24, x_27);
if (x_1006 == 0)
{
lean_object* x_1007; 
x_1007 = lean_box(0);
x_534 = x_1007;
goto block_1003;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1008 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_533);
x_1009 = lean_ctor_get(x_1008, 1);
lean_inc(x_1009);
lean_dec(x_1008);
x_1010 = l_Lean_Compiler_LCNF_Simp_simp(x_532, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1009);
if (lean_obj_tag(x_1010) == 0)
{
uint8_t x_1011; 
x_1011 = !lean_is_exclusive(x_1010);
if (x_1011 == 0)
{
lean_object* x_1012; lean_object* x_1013; 
x_1012 = lean_ctor_get(x_1010, 0);
x_1013 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1013, 0, x_1012);
lean_ctor_set(x_1010, 0, x_1013);
return x_1010;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1014 = lean_ctor_get(x_1010, 0);
x_1015 = lean_ctor_get(x_1010, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_1010);
x_1016 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1016, 0, x_1014);
x_1017 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1015);
return x_1017;
}
}
else
{
uint8_t x_1018; 
x_1018 = !lean_is_exclusive(x_1010);
if (x_1018 == 0)
{
return x_1010;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_1010, 0);
x_1020 = lean_ctor_get(x_1010, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_1010);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
}
block_1003:
{
lean_object* x_535; 
lean_dec(x_534);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_535 = l_Lean_Compiler_LCNF_Simp_simp(x_532, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_533);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
lean_inc(x_536);
x_538 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_536);
if (x_538 == 0)
{
lean_object* x_539; uint8_t x_540; 
x_539 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_537);
x_540 = !lean_is_exclusive(x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; uint8_t x_545; 
x_541 = lean_ctor_get(x_539, 1);
x_542 = lean_ctor_get(x_539, 0);
lean_dec(x_542);
x_543 = lean_ctor_get(x_21, 2);
lean_inc(x_543);
lean_dec(x_21);
x_544 = l_Lean_Compiler_LCNF_inferAppType(x_543, x_33, x_6, x_7, x_8, x_9, x_541);
x_545 = !lean_is_exclusive(x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_546 = lean_ctor_get(x_544, 0);
x_547 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
x_548 = l_Lean_Expr_headBeta(x_546);
x_549 = l_Lean_Expr_isForall(x_548);
lean_dec(x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; 
x_550 = l_Lean_Compiler_LCNF_mkAuxParam(x_546, x_530, x_6, x_7, x_8, x_9, x_547);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_553 = x_550;
} else {
 lean_dec_ref(x_550);
 x_553 = lean_box(0);
}
x_554 = lean_ctor_get(x_551, 0);
lean_inc(x_554);
x_555 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_555 == 0)
{
lean_object* x_584; 
lean_free_object(x_544);
lean_free_object(x_539);
lean_dec(x_27);
lean_dec(x_23);
x_584 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_554, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_552);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_584, 1);
lean_inc(x_585);
lean_dec(x_584);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_586 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_556 = x_587;
x_557 = x_588;
goto block_583;
}
else
{
uint8_t x_589; 
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_589 = !lean_is_exclusive(x_586);
if (x_589 == 0)
{
return x_586;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_586, 0);
x_591 = lean_ctor_get(x_586, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_586);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
else
{
uint8_t x_593; 
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_593 = !lean_is_exclusive(x_584);
if (x_593 == 0)
{
return x_584;
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_584, 0);
x_595 = lean_ctor_get(x_584, 1);
lean_inc(x_595);
lean_inc(x_594);
lean_dec(x_584);
x_596 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
return x_596;
}
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_597 = lean_array_get_size(x_23);
x_598 = l_Array_toSubarray___rarg(x_23, x_27, x_597);
x_599 = l_Array_ofSubarray___rarg(x_598);
lean_dec(x_598);
lean_ctor_set_tag(x_544, 4);
lean_ctor_set(x_544, 1, x_599);
lean_ctor_set(x_544, 0, x_554);
x_600 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_601 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_544, x_600, x_6, x_7, x_8, x_9, x_552);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_602, 0);
lean_inc(x_604);
x_605 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_604, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_603);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
lean_dec(x_605);
lean_ctor_set(x_539, 1, x_2);
lean_ctor_set(x_539, 0, x_602);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_607 = l_Lean_Compiler_LCNF_Simp_simp(x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_606);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; 
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
lean_dec(x_607);
x_556 = x_608;
x_557 = x_609;
goto block_583;
}
else
{
uint8_t x_610; 
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_610 = !lean_is_exclusive(x_607);
if (x_610 == 0)
{
return x_607;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_607, 0);
x_612 = lean_ctor_get(x_607, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_607);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
else
{
uint8_t x_614; 
lean_dec(x_602);
lean_dec(x_553);
lean_dec(x_551);
lean_free_object(x_539);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_614 = !lean_is_exclusive(x_605);
if (x_614 == 0)
{
return x_605;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_605, 0);
x_616 = lean_ctor_get(x_605, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_605);
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
lean_dec(x_553);
lean_dec(x_551);
lean_free_object(x_539);
lean_dec(x_536);
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
x_618 = !lean_is_exclusive(x_601);
if (x_618 == 0)
{
return x_601;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_601, 0);
x_620 = lean_ctor_get(x_601, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_601);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
block_583:
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_558 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_559 = lean_array_push(x_558, x_551);
x_560 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_561 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_559, x_556, x_560, x_6, x_7, x_8, x_9, x_557);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
lean_inc(x_562);
x_564 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_564, 0, x_562);
lean_closure_set(x_564, 1, x_558);
x_565 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_536, x_564, x_6, x_7, x_8, x_9, x_563);
if (lean_obj_tag(x_565) == 0)
{
uint8_t x_566; 
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_565, 0);
if (lean_is_scalar(x_553)) {
 x_568 = lean_alloc_ctor(2, 2, 0);
} else {
 x_568 = x_553;
 lean_ctor_set_tag(x_568, 2);
}
lean_ctor_set(x_568, 0, x_562);
lean_ctor_set(x_568, 1, x_567);
if (lean_is_scalar(x_22)) {
 x_569 = lean_alloc_ctor(1, 1, 0);
} else {
 x_569 = x_22;
}
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_565, 0, x_569);
return x_565;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_570 = lean_ctor_get(x_565, 0);
x_571 = lean_ctor_get(x_565, 1);
lean_inc(x_571);
lean_inc(x_570);
lean_dec(x_565);
if (lean_is_scalar(x_553)) {
 x_572 = lean_alloc_ctor(2, 2, 0);
} else {
 x_572 = x_553;
 lean_ctor_set_tag(x_572, 2);
}
lean_ctor_set(x_572, 0, x_562);
lean_ctor_set(x_572, 1, x_570);
if (lean_is_scalar(x_22)) {
 x_573 = lean_alloc_ctor(1, 1, 0);
} else {
 x_573 = x_22;
}
lean_ctor_set(x_573, 0, x_572);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_571);
return x_574;
}
}
else
{
uint8_t x_575; 
lean_dec(x_562);
lean_dec(x_553);
lean_dec(x_22);
x_575 = !lean_is_exclusive(x_565);
if (x_575 == 0)
{
return x_565;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_565, 0);
x_577 = lean_ctor_get(x_565, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_565);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_553);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_579 = !lean_is_exclusive(x_561);
if (x_579 == 0)
{
return x_561;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_561, 0);
x_581 = lean_ctor_get(x_561, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_561);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_546);
x_622 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_623 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_624 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_622, x_536, x_623, x_6, x_7, x_8, x_9, x_547);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_627 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_625, x_6, x_7, x_8, x_9, x_626);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; lean_object* x_633; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
x_631 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_631 == 0)
{
lean_object* x_646; 
lean_free_object(x_544);
lean_free_object(x_539);
lean_dec(x_27);
lean_dec(x_23);
x_646 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_630, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_629);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
lean_dec(x_646);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_648 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_647);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_632 = x_649;
x_633 = x_650;
goto block_645;
}
else
{
uint8_t x_651; 
lean_dec(x_628);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_651 = !lean_is_exclusive(x_648);
if (x_651 == 0)
{
return x_648;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_648, 0);
x_653 = lean_ctor_get(x_648, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_648);
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_652);
lean_ctor_set(x_654, 1, x_653);
return x_654;
}
}
}
else
{
uint8_t x_655; 
lean_dec(x_628);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_655 = !lean_is_exclusive(x_646);
if (x_655 == 0)
{
return x_646;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_646, 0);
x_657 = lean_ctor_get(x_646, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_646);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
return x_658;
}
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_659 = lean_array_get_size(x_23);
x_660 = l_Array_toSubarray___rarg(x_23, x_27, x_659);
x_661 = l_Array_ofSubarray___rarg(x_660);
lean_dec(x_660);
lean_ctor_set_tag(x_544, 4);
lean_ctor_set(x_544, 1, x_661);
lean_ctor_set(x_544, 0, x_630);
x_662 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_663 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_544, x_662, x_6, x_7, x_8, x_9, x_629);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
lean_dec(x_663);
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
x_667 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_666, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_665);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
lean_dec(x_667);
lean_ctor_set(x_539, 1, x_2);
lean_ctor_set(x_539, 0, x_664);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_669 = l_Lean_Compiler_LCNF_Simp_simp(x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_668);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_632 = x_670;
x_633 = x_671;
goto block_645;
}
else
{
uint8_t x_672; 
lean_dec(x_628);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_672 = !lean_is_exclusive(x_669);
if (x_672 == 0)
{
return x_669;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_669, 0);
x_674 = lean_ctor_get(x_669, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_669);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
else
{
uint8_t x_676; 
lean_dec(x_664);
lean_dec(x_628);
lean_free_object(x_539);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_676 = !lean_is_exclusive(x_667);
if (x_676 == 0)
{
return x_667;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_667, 0);
x_678 = lean_ctor_get(x_667, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_667);
x_679 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
return x_679;
}
}
}
else
{
uint8_t x_680; 
lean_dec(x_628);
lean_free_object(x_539);
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
x_680 = !lean_is_exclusive(x_663);
if (x_680 == 0)
{
return x_663;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_663, 0);
x_682 = lean_ctor_get(x_663, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_663);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set(x_683, 1, x_682);
return x_683;
}
}
}
block_645:
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; 
x_634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_634, 0, x_628);
x_635 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_636 = lean_array_push(x_635, x_634);
x_637 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_636, x_632, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_633);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_636);
x_638 = !lean_is_exclusive(x_637);
if (x_638 == 0)
{
lean_object* x_639; lean_object* x_640; 
x_639 = lean_ctor_get(x_637, 0);
if (lean_is_scalar(x_22)) {
 x_640 = lean_alloc_ctor(1, 1, 0);
} else {
 x_640 = x_22;
}
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_637, 0, x_640);
return x_637;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_641 = lean_ctor_get(x_637, 0);
x_642 = lean_ctor_get(x_637, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_637);
if (lean_is_scalar(x_22)) {
 x_643 = lean_alloc_ctor(1, 1, 0);
} else {
 x_643 = x_22;
}
lean_ctor_set(x_643, 0, x_641);
x_644 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_642);
return x_644;
}
}
}
else
{
uint8_t x_684; 
lean_free_object(x_544);
lean_free_object(x_539);
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
x_684 = !lean_is_exclusive(x_627);
if (x_684 == 0)
{
return x_627;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_627, 0);
x_686 = lean_ctor_get(x_627, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_627);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
else
{
uint8_t x_688; 
lean_free_object(x_544);
lean_free_object(x_539);
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
x_688 = !lean_is_exclusive(x_624);
if (x_688 == 0)
{
return x_624;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_624, 0);
x_690 = lean_ctor_get(x_624, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_624);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
}
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; 
x_692 = lean_ctor_get(x_544, 0);
x_693 = lean_ctor_get(x_544, 1);
lean_inc(x_693);
lean_inc(x_692);
lean_dec(x_544);
lean_inc(x_692);
x_694 = l_Lean_Expr_headBeta(x_692);
x_695 = l_Lean_Expr_isForall(x_694);
lean_dec(x_694);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; lean_object* x_702; lean_object* x_703; 
x_696 = l_Lean_Compiler_LCNF_mkAuxParam(x_692, x_530, x_6, x_7, x_8, x_9, x_693);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_699 = x_696;
} else {
 lean_dec_ref(x_696);
 x_699 = lean_box(0);
}
x_700 = lean_ctor_get(x_697, 0);
lean_inc(x_700);
x_701 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_701 == 0)
{
lean_object* x_727; 
lean_free_object(x_539);
lean_dec(x_27);
lean_dec(x_23);
x_727 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_700, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_698);
if (lean_obj_tag(x_727) == 0)
{
lean_object* x_728; lean_object* x_729; 
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
lean_dec(x_727);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_729 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_728);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_702 = x_730;
x_703 = x_731;
goto block_726;
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_699);
lean_dec(x_697);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_732 = lean_ctor_get(x_729, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_729, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_734 = x_729;
} else {
 lean_dec_ref(x_729);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(1, 2, 0);
} else {
 x_735 = x_734;
}
lean_ctor_set(x_735, 0, x_732);
lean_ctor_set(x_735, 1, x_733);
return x_735;
}
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_699);
lean_dec(x_697);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_736 = lean_ctor_get(x_727, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_727, 1);
lean_inc(x_737);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_738 = x_727;
} else {
 lean_dec_ref(x_727);
 x_738 = lean_box(0);
}
if (lean_is_scalar(x_738)) {
 x_739 = lean_alloc_ctor(1, 2, 0);
} else {
 x_739 = x_738;
}
lean_ctor_set(x_739, 0, x_736);
lean_ctor_set(x_739, 1, x_737);
return x_739;
}
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_740 = lean_array_get_size(x_23);
x_741 = l_Array_toSubarray___rarg(x_23, x_27, x_740);
x_742 = l_Array_ofSubarray___rarg(x_741);
lean_dec(x_741);
x_743 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_743, 0, x_700);
lean_ctor_set(x_743, 1, x_742);
x_744 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_745 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_743, x_744, x_6, x_7, x_8, x_9, x_698);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec(x_745);
x_748 = lean_ctor_get(x_746, 0);
lean_inc(x_748);
x_749 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_748, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_747);
if (lean_obj_tag(x_749) == 0)
{
lean_object* x_750; lean_object* x_751; 
x_750 = lean_ctor_get(x_749, 1);
lean_inc(x_750);
lean_dec(x_749);
lean_ctor_set(x_539, 1, x_2);
lean_ctor_set(x_539, 0, x_746);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_751 = l_Lean_Compiler_LCNF_Simp_simp(x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_750);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
x_702 = x_752;
x_703 = x_753;
goto block_726;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_699);
lean_dec(x_697);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_754 = lean_ctor_get(x_751, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_751, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_756 = x_751;
} else {
 lean_dec_ref(x_751);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 2, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_754);
lean_ctor_set(x_757, 1, x_755);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_746);
lean_dec(x_699);
lean_dec(x_697);
lean_free_object(x_539);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_758 = lean_ctor_get(x_749, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_749, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_760 = x_749;
} else {
 lean_dec_ref(x_749);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_699);
lean_dec(x_697);
lean_free_object(x_539);
lean_dec(x_536);
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
x_762 = lean_ctor_get(x_745, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_745, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_764 = x_745;
} else {
 lean_dec_ref(x_745);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
block_726:
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_704 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_705 = lean_array_push(x_704, x_697);
x_706 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_707 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_705, x_702, x_706, x_6, x_7, x_8, x_9, x_703);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_708 = lean_ctor_get(x_707, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_707, 1);
lean_inc(x_709);
lean_dec(x_707);
lean_inc(x_708);
x_710 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_710, 0, x_708);
lean_closure_set(x_710, 1, x_704);
x_711 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_536, x_710, x_6, x_7, x_8, x_9, x_709);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_714 = x_711;
} else {
 lean_dec_ref(x_711);
 x_714 = lean_box(0);
}
if (lean_is_scalar(x_699)) {
 x_715 = lean_alloc_ctor(2, 2, 0);
} else {
 x_715 = x_699;
 lean_ctor_set_tag(x_715, 2);
}
lean_ctor_set(x_715, 0, x_708);
lean_ctor_set(x_715, 1, x_712);
if (lean_is_scalar(x_22)) {
 x_716 = lean_alloc_ctor(1, 1, 0);
} else {
 x_716 = x_22;
}
lean_ctor_set(x_716, 0, x_715);
if (lean_is_scalar(x_714)) {
 x_717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_717 = x_714;
}
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_713);
return x_717;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
lean_dec(x_708);
lean_dec(x_699);
lean_dec(x_22);
x_718 = lean_ctor_get(x_711, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_711, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_711)) {
 lean_ctor_release(x_711, 0);
 lean_ctor_release(x_711, 1);
 x_720 = x_711;
} else {
 lean_dec_ref(x_711);
 x_720 = lean_box(0);
}
if (lean_is_scalar(x_720)) {
 x_721 = lean_alloc_ctor(1, 2, 0);
} else {
 x_721 = x_720;
}
lean_ctor_set(x_721, 0, x_718);
lean_ctor_set(x_721, 1, x_719);
return x_721;
}
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
lean_dec(x_699);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_722 = lean_ctor_get(x_707, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_707, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_724 = x_707;
} else {
 lean_dec_ref(x_707);
 x_724 = lean_box(0);
}
if (lean_is_scalar(x_724)) {
 x_725 = lean_alloc_ctor(1, 2, 0);
} else {
 x_725 = x_724;
}
lean_ctor_set(x_725, 0, x_722);
lean_ctor_set(x_725, 1, x_723);
return x_725;
}
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_692);
x_766 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_767 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_768 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_766, x_536, x_767, x_6, x_7, x_8, x_9, x_693);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_769 = lean_ctor_get(x_768, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_768, 1);
lean_inc(x_770);
lean_dec(x_768);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_771 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_769, x_6, x_7, x_8, x_9, x_770);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; uint8_t x_775; lean_object* x_776; lean_object* x_777; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_774 = lean_ctor_get(x_772, 0);
lean_inc(x_774);
x_775 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_775 == 0)
{
lean_object* x_788; 
lean_free_object(x_539);
lean_dec(x_27);
lean_dec(x_23);
x_788 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_774, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_773);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_ctor_get(x_788, 1);
lean_inc(x_789);
lean_dec(x_788);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_790 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_789);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
lean_dec(x_790);
x_776 = x_791;
x_777 = x_792;
goto block_787;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_772);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_793 = lean_ctor_get(x_790, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_790, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_795 = x_790;
} else {
 lean_dec_ref(x_790);
 x_795 = lean_box(0);
}
if (lean_is_scalar(x_795)) {
 x_796 = lean_alloc_ctor(1, 2, 0);
} else {
 x_796 = x_795;
}
lean_ctor_set(x_796, 0, x_793);
lean_ctor_set(x_796, 1, x_794);
return x_796;
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_772);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_797 = lean_ctor_get(x_788, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_788, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_799 = x_788;
} else {
 lean_dec_ref(x_788);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_798);
return x_800;
}
}
else
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_801 = lean_array_get_size(x_23);
x_802 = l_Array_toSubarray___rarg(x_23, x_27, x_801);
x_803 = l_Array_ofSubarray___rarg(x_802);
lean_dec(x_802);
x_804 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_804, 0, x_774);
lean_ctor_set(x_804, 1, x_803);
x_805 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_806 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_804, x_805, x_6, x_7, x_8, x_9, x_773);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
x_809 = lean_ctor_get(x_807, 0);
lean_inc(x_809);
x_810 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_809, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_808);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; lean_object* x_812; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
lean_ctor_set(x_539, 1, x_2);
lean_ctor_set(x_539, 0, x_807);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_812 = l_Lean_Compiler_LCNF_Simp_simp(x_539, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_811);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_812, 1);
lean_inc(x_814);
lean_dec(x_812);
x_776 = x_813;
x_777 = x_814;
goto block_787;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_772);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_815 = lean_ctor_get(x_812, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_812, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_817 = x_812;
} else {
 lean_dec_ref(x_812);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(1, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
lean_dec(x_807);
lean_dec(x_772);
lean_free_object(x_539);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_819 = lean_ctor_get(x_810, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_810, 1);
lean_inc(x_820);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_821 = x_810;
} else {
 lean_dec_ref(x_810);
 x_821 = lean_box(0);
}
if (lean_is_scalar(x_821)) {
 x_822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_822 = x_821;
}
lean_ctor_set(x_822, 0, x_819);
lean_ctor_set(x_822, 1, x_820);
return x_822;
}
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_772);
lean_free_object(x_539);
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
x_823 = lean_ctor_get(x_806, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_806, 1);
lean_inc(x_824);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_825 = x_806;
} else {
 lean_dec_ref(x_806);
 x_825 = lean_box(0);
}
if (lean_is_scalar(x_825)) {
 x_826 = lean_alloc_ctor(1, 2, 0);
} else {
 x_826 = x_825;
}
lean_ctor_set(x_826, 0, x_823);
lean_ctor_set(x_826, 1, x_824);
return x_826;
}
}
block_787:
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_778 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_778, 0, x_772);
x_779 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_780 = lean_array_push(x_779, x_778);
x_781 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_780, x_776, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_777);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_780);
x_782 = lean_ctor_get(x_781, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_781, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_784 = x_781;
} else {
 lean_dec_ref(x_781);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_785 = lean_alloc_ctor(1, 1, 0);
} else {
 x_785 = x_22;
}
lean_ctor_set(x_785, 0, x_782);
if (lean_is_scalar(x_784)) {
 x_786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_786 = x_784;
}
lean_ctor_set(x_786, 0, x_785);
lean_ctor_set(x_786, 1, x_783);
return x_786;
}
}
else
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
lean_free_object(x_539);
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
x_827 = lean_ctor_get(x_771, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_771, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_829 = x_771;
} else {
 lean_dec_ref(x_771);
 x_829 = lean_box(0);
}
if (lean_is_scalar(x_829)) {
 x_830 = lean_alloc_ctor(1, 2, 0);
} else {
 x_830 = x_829;
}
lean_ctor_set(x_830, 0, x_827);
lean_ctor_set(x_830, 1, x_828);
return x_830;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_free_object(x_539);
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
x_831 = lean_ctor_get(x_768, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_768, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 x_833 = x_768;
} else {
 lean_dec_ref(x_768);
 x_833 = lean_box(0);
}
if (lean_is_scalar(x_833)) {
 x_834 = lean_alloc_ctor(1, 2, 0);
} else {
 x_834 = x_833;
}
lean_ctor_set(x_834, 0, x_831);
lean_ctor_set(x_834, 1, x_832);
return x_834;
}
}
}
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; 
x_835 = lean_ctor_get(x_539, 1);
lean_inc(x_835);
lean_dec(x_539);
x_836 = lean_ctor_get(x_21, 2);
lean_inc(x_836);
lean_dec(x_21);
x_837 = l_Lean_Compiler_LCNF_inferAppType(x_836, x_33, x_6, x_7, x_8, x_9, x_835);
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_840 = x_837;
} else {
 lean_dec_ref(x_837);
 x_840 = lean_box(0);
}
lean_inc(x_838);
x_841 = l_Lean_Expr_headBeta(x_838);
x_842 = l_Lean_Expr_isForall(x_841);
lean_dec(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; lean_object* x_849; lean_object* x_850; 
x_843 = l_Lean_Compiler_LCNF_mkAuxParam(x_838, x_530, x_6, x_7, x_8, x_9, x_839);
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_846 = x_843;
} else {
 lean_dec_ref(x_843);
 x_846 = lean_box(0);
}
x_847 = lean_ctor_get(x_844, 0);
lean_inc(x_847);
x_848 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_848 == 0)
{
lean_object* x_874; 
lean_dec(x_840);
lean_dec(x_27);
lean_dec(x_23);
x_874 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_847, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_845);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_874, 1);
lean_inc(x_875);
lean_dec(x_874);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_876 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_849 = x_877;
x_850 = x_878;
goto block_873;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_879 = lean_ctor_get(x_876, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_876, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_881 = x_876;
} else {
 lean_dec_ref(x_876);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_881)) {
 x_882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_882 = x_881;
}
lean_ctor_set(x_882, 0, x_879);
lean_ctor_set(x_882, 1, x_880);
return x_882;
}
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_883 = lean_ctor_get(x_874, 0);
lean_inc(x_883);
x_884 = lean_ctor_get(x_874, 1);
lean_inc(x_884);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_885 = x_874;
} else {
 lean_dec_ref(x_874);
 x_885 = lean_box(0);
}
if (lean_is_scalar(x_885)) {
 x_886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_886 = x_885;
}
lean_ctor_set(x_886, 0, x_883);
lean_ctor_set(x_886, 1, x_884);
return x_886;
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_887 = lean_array_get_size(x_23);
x_888 = l_Array_toSubarray___rarg(x_23, x_27, x_887);
x_889 = l_Array_ofSubarray___rarg(x_888);
lean_dec(x_888);
if (lean_is_scalar(x_840)) {
 x_890 = lean_alloc_ctor(4, 2, 0);
} else {
 x_890 = x_840;
 lean_ctor_set_tag(x_890, 4);
}
lean_ctor_set(x_890, 0, x_847);
lean_ctor_set(x_890, 1, x_889);
x_891 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_892 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_890, x_891, x_6, x_7, x_8, x_9, x_845);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
x_893 = lean_ctor_get(x_892, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_892, 1);
lean_inc(x_894);
lean_dec(x_892);
x_895 = lean_ctor_get(x_893, 0);
lean_inc(x_895);
x_896 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_895, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_894);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
lean_dec(x_896);
x_898 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_898, 0, x_893);
lean_ctor_set(x_898, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_899 = l_Lean_Compiler_LCNF_Simp_simp(x_898, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_897);
if (lean_obj_tag(x_899) == 0)
{
lean_object* x_900; lean_object* x_901; 
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
lean_dec(x_899);
x_849 = x_900;
x_850 = x_901;
goto block_873;
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_902 = lean_ctor_get(x_899, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_899, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_904 = x_899;
} else {
 lean_dec_ref(x_899);
 x_904 = lean_box(0);
}
if (lean_is_scalar(x_904)) {
 x_905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_905 = x_904;
}
lean_ctor_set(x_905, 0, x_902);
lean_ctor_set(x_905, 1, x_903);
return x_905;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_893);
lean_dec(x_846);
lean_dec(x_844);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_906 = lean_ctor_get(x_896, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_896, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_908 = x_896;
} else {
 lean_dec_ref(x_896);
 x_908 = lean_box(0);
}
if (lean_is_scalar(x_908)) {
 x_909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_909 = x_908;
}
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_907);
return x_909;
}
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_846);
lean_dec(x_844);
lean_dec(x_536);
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
x_910 = lean_ctor_get(x_892, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_892, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 x_912 = x_892;
} else {
 lean_dec_ref(x_892);
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
block_873:
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_851 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_852 = lean_array_push(x_851, x_844);
x_853 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_854 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_852, x_849, x_853, x_6, x_7, x_8, x_9, x_850);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
lean_inc(x_855);
x_857 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_857, 0, x_855);
lean_closure_set(x_857, 1, x_851);
x_858 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_536, x_857, x_6, x_7, x_8, x_9, x_856);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_861 = x_858;
} else {
 lean_dec_ref(x_858);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_862 = lean_alloc_ctor(2, 2, 0);
} else {
 x_862 = x_846;
 lean_ctor_set_tag(x_862, 2);
}
lean_ctor_set(x_862, 0, x_855);
lean_ctor_set(x_862, 1, x_859);
if (lean_is_scalar(x_22)) {
 x_863 = lean_alloc_ctor(1, 1, 0);
} else {
 x_863 = x_22;
}
lean_ctor_set(x_863, 0, x_862);
if (lean_is_scalar(x_861)) {
 x_864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_864 = x_861;
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_860);
return x_864;
}
else
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
lean_dec(x_855);
lean_dec(x_846);
lean_dec(x_22);
x_865 = lean_ctor_get(x_858, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_858, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_867 = x_858;
} else {
 lean_dec_ref(x_858);
 x_867 = lean_box(0);
}
if (lean_is_scalar(x_867)) {
 x_868 = lean_alloc_ctor(1, 2, 0);
} else {
 x_868 = x_867;
}
lean_ctor_set(x_868, 0, x_865);
lean_ctor_set(x_868, 1, x_866);
return x_868;
}
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_846);
lean_dec(x_536);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_869 = lean_ctor_get(x_854, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_854, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_871 = x_854;
} else {
 lean_dec_ref(x_854);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
return x_872;
}
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; 
lean_dec(x_838);
x_914 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_915 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_916 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_914, x_536, x_915, x_6, x_7, x_8, x_9, x_839);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
lean_dec(x_916);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_919 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_917, x_6, x_7, x_8, x_9, x_918);
if (lean_obj_tag(x_919) == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; uint8_t x_923; lean_object* x_924; lean_object* x_925; 
x_920 = lean_ctor_get(x_919, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_919, 1);
lean_inc(x_921);
lean_dec(x_919);
x_922 = lean_ctor_get(x_920, 0);
lean_inc(x_922);
x_923 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_923 == 0)
{
lean_object* x_936; 
lean_dec(x_840);
lean_dec(x_27);
lean_dec(x_23);
x_936 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_922, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_921);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; 
x_937 = lean_ctor_get(x_936, 1);
lean_inc(x_937);
lean_dec(x_936);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_938 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_937);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
x_924 = x_939;
x_925 = x_940;
goto block_935;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_920);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_920);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_945 = lean_ctor_get(x_936, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_936, 1);
lean_inc(x_946);
if (lean_is_exclusive(x_936)) {
 lean_ctor_release(x_936, 0);
 lean_ctor_release(x_936, 1);
 x_947 = x_936;
} else {
 lean_dec_ref(x_936);
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
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
x_949 = lean_array_get_size(x_23);
x_950 = l_Array_toSubarray___rarg(x_23, x_27, x_949);
x_951 = l_Array_ofSubarray___rarg(x_950);
lean_dec(x_950);
if (lean_is_scalar(x_840)) {
 x_952 = lean_alloc_ctor(4, 2, 0);
} else {
 x_952 = x_840;
 lean_ctor_set_tag(x_952, 4);
}
lean_ctor_set(x_952, 0, x_922);
lean_ctor_set(x_952, 1, x_951);
x_953 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_954 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_952, x_953, x_6, x_7, x_8, x_9, x_921);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
x_957 = lean_ctor_get(x_955, 0);
lean_inc(x_957);
x_958 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_957, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_956);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec(x_958);
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_955);
lean_ctor_set(x_960, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_961 = l_Lean_Compiler_LCNF_Simp_simp(x_960, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_959);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_924 = x_962;
x_925 = x_963;
goto block_935;
}
else
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; 
lean_dec(x_920);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_964 = lean_ctor_get(x_961, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_961, 1);
lean_inc(x_965);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 x_966 = x_961;
} else {
 lean_dec_ref(x_961);
 x_966 = lean_box(0);
}
if (lean_is_scalar(x_966)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_966;
}
lean_ctor_set(x_967, 0, x_964);
lean_ctor_set(x_967, 1, x_965);
return x_967;
}
}
else
{
lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_955);
lean_dec(x_920);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_968 = lean_ctor_get(x_958, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_958, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_970 = x_958;
} else {
 lean_dec_ref(x_958);
 x_970 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_971 = lean_alloc_ctor(1, 2, 0);
} else {
 x_971 = x_970;
}
lean_ctor_set(x_971, 0, x_968);
lean_ctor_set(x_971, 1, x_969);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_920);
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
x_972 = lean_ctor_get(x_954, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_954, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_974 = x_954;
} else {
 lean_dec_ref(x_954);
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
block_935:
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_926 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_926, 0, x_920);
x_927 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_928 = lean_array_push(x_927, x_926);
x_929 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_928, x_924, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_925);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_928);
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_932 = x_929;
} else {
 lean_dec_ref(x_929);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_933 = lean_alloc_ctor(1, 1, 0);
} else {
 x_933 = x_22;
}
lean_ctor_set(x_933, 0, x_930);
if (lean_is_scalar(x_932)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_932;
}
lean_ctor_set(x_934, 0, x_933);
lean_ctor_set(x_934, 1, x_931);
return x_934;
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_840);
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
x_976 = lean_ctor_get(x_919, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_919, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_919)) {
 lean_ctor_release(x_919, 0);
 lean_ctor_release(x_919, 1);
 x_978 = x_919;
} else {
 lean_dec_ref(x_919);
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
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_840);
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
x_980 = lean_ctor_get(x_916, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_916, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_982 = x_916;
} else {
 lean_dec_ref(x_916);
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
}
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
lean_dec(x_33);
lean_dec(x_21);
x_984 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_537);
x_985 = lean_ctor_get(x_984, 1);
lean_inc(x_985);
lean_dec(x_984);
x_986 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_986, 0, x_3);
lean_closure_set(x_986, 1, x_4);
lean_closure_set(x_986, 2, x_5);
lean_closure_set(x_986, 3, x_27);
lean_closure_set(x_986, 4, x_24);
lean_closure_set(x_986, 5, x_26);
lean_closure_set(x_986, 6, x_2);
lean_closure_set(x_986, 7, x_23);
x_987 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_536, x_986, x_6, x_7, x_8, x_9, x_985);
if (lean_obj_tag(x_987) == 0)
{
uint8_t x_988; 
x_988 = !lean_is_exclusive(x_987);
if (x_988 == 0)
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_987, 0);
if (lean_is_scalar(x_22)) {
 x_990 = lean_alloc_ctor(1, 1, 0);
} else {
 x_990 = x_22;
}
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_987, 0, x_990);
return x_987;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_991 = lean_ctor_get(x_987, 0);
x_992 = lean_ctor_get(x_987, 1);
lean_inc(x_992);
lean_inc(x_991);
lean_dec(x_987);
if (lean_is_scalar(x_22)) {
 x_993 = lean_alloc_ctor(1, 1, 0);
} else {
 x_993 = x_22;
}
lean_ctor_set(x_993, 0, x_991);
x_994 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_994, 0, x_993);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
}
else
{
uint8_t x_995; 
lean_dec(x_22);
x_995 = !lean_is_exclusive(x_987);
if (x_995 == 0)
{
return x_987;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_987, 0);
x_997 = lean_ctor_get(x_987, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_987);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_996);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
}
else
{
uint8_t x_999; 
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
x_999 = !lean_is_exclusive(x_535);
if (x_999 == 0)
{
return x_535;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_535, 0);
x_1001 = lean_ctor_get(x_535, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_535);
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
uint8_t x_1022; 
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
x_1022 = !lean_is_exclusive(x_531);
if (x_1022 == 0)
{
return x_531;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_531, 0);
x_1024 = lean_ctor_get(x_531, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_531);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
case 2:
{
uint8_t x_1026; lean_object* x_1027; 
lean_dec(x_11);
x_1026 = 0;
lean_inc(x_33);
x_1027 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1026, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_1027) == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; uint8_t x_1500; 
x_1028 = lean_ctor_get(x_1027, 0);
lean_inc(x_1028);
x_1029 = lean_ctor_get(x_1027, 1);
lean_inc(x_1029);
lean_dec(x_1027);
x_1500 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1500 == 0)
{
lean_object* x_1501; 
x_1501 = lean_box(0);
x_1030 = x_1501;
goto block_1499;
}
else
{
uint8_t x_1502; 
x_1502 = lean_nat_dec_eq(x_24, x_27);
if (x_1502 == 0)
{
lean_object* x_1503; 
x_1503 = lean_box(0);
x_1030 = x_1503;
goto block_1499;
}
else
{
lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1504 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1029);
x_1505 = lean_ctor_get(x_1504, 1);
lean_inc(x_1505);
lean_dec(x_1504);
x_1506 = l_Lean_Compiler_LCNF_Simp_simp(x_1028, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1505);
if (lean_obj_tag(x_1506) == 0)
{
uint8_t x_1507; 
x_1507 = !lean_is_exclusive(x_1506);
if (x_1507 == 0)
{
lean_object* x_1508; lean_object* x_1509; 
x_1508 = lean_ctor_get(x_1506, 0);
x_1509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1509, 0, x_1508);
lean_ctor_set(x_1506, 0, x_1509);
return x_1506;
}
else
{
lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1510 = lean_ctor_get(x_1506, 0);
x_1511 = lean_ctor_get(x_1506, 1);
lean_inc(x_1511);
lean_inc(x_1510);
lean_dec(x_1506);
x_1512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1512, 0, x_1510);
x_1513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1513, 0, x_1512);
lean_ctor_set(x_1513, 1, x_1511);
return x_1513;
}
}
else
{
uint8_t x_1514; 
x_1514 = !lean_is_exclusive(x_1506);
if (x_1514 == 0)
{
return x_1506;
}
else
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1515 = lean_ctor_get(x_1506, 0);
x_1516 = lean_ctor_get(x_1506, 1);
lean_inc(x_1516);
lean_inc(x_1515);
lean_dec(x_1506);
x_1517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1517, 0, x_1515);
lean_ctor_set(x_1517, 1, x_1516);
return x_1517;
}
}
}
}
block_1499:
{
lean_object* x_1031; 
lean_dec(x_1030);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1031 = l_Lean_Compiler_LCNF_Simp_simp(x_1028, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1029);
if (lean_obj_tag(x_1031) == 0)
{
lean_object* x_1032; lean_object* x_1033; uint8_t x_1034; 
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
lean_inc(x_1032);
x_1034 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1032);
if (x_1034 == 0)
{
lean_object* x_1035; uint8_t x_1036; 
x_1035 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1033);
x_1036 = !lean_is_exclusive(x_1035);
if (x_1036 == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; 
x_1037 = lean_ctor_get(x_1035, 1);
x_1038 = lean_ctor_get(x_1035, 0);
lean_dec(x_1038);
x_1039 = lean_ctor_get(x_21, 2);
lean_inc(x_1039);
lean_dec(x_21);
x_1040 = l_Lean_Compiler_LCNF_inferAppType(x_1039, x_33, x_6, x_7, x_8, x_9, x_1037);
x_1041 = !lean_is_exclusive(x_1040);
if (x_1041 == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; uint8_t x_1045; 
x_1042 = lean_ctor_get(x_1040, 0);
x_1043 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
x_1044 = l_Lean_Expr_headBeta(x_1042);
x_1045 = l_Lean_Expr_isForall(x_1044);
lean_dec(x_1044);
if (x_1045 == 0)
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; uint8_t x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1046 = l_Lean_Compiler_LCNF_mkAuxParam(x_1042, x_1026, x_6, x_7, x_8, x_9, x_1043);
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1049 = x_1046;
} else {
 lean_dec_ref(x_1046);
 x_1049 = lean_box(0);
}
x_1050 = lean_ctor_get(x_1047, 0);
lean_inc(x_1050);
x_1051 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1051 == 0)
{
lean_object* x_1080; 
lean_free_object(x_1040);
lean_free_object(x_1035);
lean_dec(x_27);
lean_dec(x_23);
x_1080 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1050, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1048);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; 
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
lean_dec(x_1080);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1082 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1081);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1052 = x_1083;
x_1053 = x_1084;
goto block_1079;
}
else
{
uint8_t x_1085; 
lean_dec(x_1049);
lean_dec(x_1047);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1085 = !lean_is_exclusive(x_1082);
if (x_1085 == 0)
{
return x_1082;
}
else
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; 
x_1086 = lean_ctor_get(x_1082, 0);
x_1087 = lean_ctor_get(x_1082, 1);
lean_inc(x_1087);
lean_inc(x_1086);
lean_dec(x_1082);
x_1088 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1088, 0, x_1086);
lean_ctor_set(x_1088, 1, x_1087);
return x_1088;
}
}
}
else
{
uint8_t x_1089; 
lean_dec(x_1049);
lean_dec(x_1047);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1089 = !lean_is_exclusive(x_1080);
if (x_1089 == 0)
{
return x_1080;
}
else
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1090 = lean_ctor_get(x_1080, 0);
x_1091 = lean_ctor_get(x_1080, 1);
lean_inc(x_1091);
lean_inc(x_1090);
lean_dec(x_1080);
x_1092 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1092, 0, x_1090);
lean_ctor_set(x_1092, 1, x_1091);
return x_1092;
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1093 = lean_array_get_size(x_23);
x_1094 = l_Array_toSubarray___rarg(x_23, x_27, x_1093);
x_1095 = l_Array_ofSubarray___rarg(x_1094);
lean_dec(x_1094);
lean_ctor_set_tag(x_1040, 4);
lean_ctor_set(x_1040, 1, x_1095);
lean_ctor_set(x_1040, 0, x_1050);
x_1096 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1097 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1040, x_1096, x_6, x_7, x_8, x_9, x_1048);
if (lean_obj_tag(x_1097) == 0)
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1097, 1);
lean_inc(x_1099);
lean_dec(x_1097);
x_1100 = lean_ctor_get(x_1098, 0);
lean_inc(x_1100);
x_1101 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1100, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1099);
if (lean_obj_tag(x_1101) == 0)
{
lean_object* x_1102; lean_object* x_1103; 
x_1102 = lean_ctor_get(x_1101, 1);
lean_inc(x_1102);
lean_dec(x_1101);
lean_ctor_set(x_1035, 1, x_2);
lean_ctor_set(x_1035, 0, x_1098);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1103 = l_Lean_Compiler_LCNF_Simp_simp(x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1102);
if (lean_obj_tag(x_1103) == 0)
{
lean_object* x_1104; lean_object* x_1105; 
x_1104 = lean_ctor_get(x_1103, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1103, 1);
lean_inc(x_1105);
lean_dec(x_1103);
x_1052 = x_1104;
x_1053 = x_1105;
goto block_1079;
}
else
{
uint8_t x_1106; 
lean_dec(x_1049);
lean_dec(x_1047);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1106 = !lean_is_exclusive(x_1103);
if (x_1106 == 0)
{
return x_1103;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1103, 0);
x_1108 = lean_ctor_get(x_1103, 1);
lean_inc(x_1108);
lean_inc(x_1107);
lean_dec(x_1103);
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
lean_dec(x_1098);
lean_dec(x_1049);
lean_dec(x_1047);
lean_free_object(x_1035);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1110 = !lean_is_exclusive(x_1101);
if (x_1110 == 0)
{
return x_1101;
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; 
x_1111 = lean_ctor_get(x_1101, 0);
x_1112 = lean_ctor_get(x_1101, 1);
lean_inc(x_1112);
lean_inc(x_1111);
lean_dec(x_1101);
x_1113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
return x_1113;
}
}
}
else
{
uint8_t x_1114; 
lean_dec(x_1049);
lean_dec(x_1047);
lean_free_object(x_1035);
lean_dec(x_1032);
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
x_1114 = !lean_is_exclusive(x_1097);
if (x_1114 == 0)
{
return x_1097;
}
else
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1115 = lean_ctor_get(x_1097, 0);
x_1116 = lean_ctor_get(x_1097, 1);
lean_inc(x_1116);
lean_inc(x_1115);
lean_dec(x_1097);
x_1117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1117, 0, x_1115);
lean_ctor_set(x_1117, 1, x_1116);
return x_1117;
}
}
}
block_1079:
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1054 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1055 = lean_array_push(x_1054, x_1047);
x_1056 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1057 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1055, x_1052, x_1056, x_6, x_7, x_8, x_9, x_1053);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
x_1059 = lean_ctor_get(x_1057, 1);
lean_inc(x_1059);
lean_dec(x_1057);
lean_inc(x_1058);
x_1060 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1060, 0, x_1058);
lean_closure_set(x_1060, 1, x_1054);
x_1061 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1032, x_1060, x_6, x_7, x_8, x_9, x_1059);
if (lean_obj_tag(x_1061) == 0)
{
uint8_t x_1062; 
x_1062 = !lean_is_exclusive(x_1061);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1061, 0);
if (lean_is_scalar(x_1049)) {
 x_1064 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1064 = x_1049;
 lean_ctor_set_tag(x_1064, 2);
}
lean_ctor_set(x_1064, 0, x_1058);
lean_ctor_set(x_1064, 1, x_1063);
if (lean_is_scalar(x_22)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_22;
}
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1061, 0, x_1065);
return x_1061;
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1066 = lean_ctor_get(x_1061, 0);
x_1067 = lean_ctor_get(x_1061, 1);
lean_inc(x_1067);
lean_inc(x_1066);
lean_dec(x_1061);
if (lean_is_scalar(x_1049)) {
 x_1068 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1068 = x_1049;
 lean_ctor_set_tag(x_1068, 2);
}
lean_ctor_set(x_1068, 0, x_1058);
lean_ctor_set(x_1068, 1, x_1066);
if (lean_is_scalar(x_22)) {
 x_1069 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1069 = x_22;
}
lean_ctor_set(x_1069, 0, x_1068);
x_1070 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_1067);
return x_1070;
}
}
else
{
uint8_t x_1071; 
lean_dec(x_1058);
lean_dec(x_1049);
lean_dec(x_22);
x_1071 = !lean_is_exclusive(x_1061);
if (x_1071 == 0)
{
return x_1061;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1072 = lean_ctor_get(x_1061, 0);
x_1073 = lean_ctor_get(x_1061, 1);
lean_inc(x_1073);
lean_inc(x_1072);
lean_dec(x_1061);
x_1074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1074, 0, x_1072);
lean_ctor_set(x_1074, 1, x_1073);
return x_1074;
}
}
}
else
{
uint8_t x_1075; 
lean_dec(x_1049);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1075 = !lean_is_exclusive(x_1057);
if (x_1075 == 0)
{
return x_1057;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1076 = lean_ctor_get(x_1057, 0);
x_1077 = lean_ctor_get(x_1057, 1);
lean_inc(x_1077);
lean_inc(x_1076);
lean_dec(x_1057);
x_1078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1078, 0, x_1076);
lean_ctor_set(x_1078, 1, x_1077);
return x_1078;
}
}
}
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_1042);
x_1118 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1119 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1120 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1118, x_1032, x_1119, x_6, x_7, x_8, x_9, x_1043);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
x_1122 = lean_ctor_get(x_1120, 1);
lean_inc(x_1122);
lean_dec(x_1120);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1123 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1121, x_6, x_7, x_8, x_9, x_1122);
if (lean_obj_tag(x_1123) == 0)
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; uint8_t x_1127; lean_object* x_1128; lean_object* x_1129; 
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
lean_object* x_1142; 
lean_free_object(x_1040);
lean_free_object(x_1035);
lean_dec(x_27);
lean_dec(x_23);
x_1142 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1126, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1125);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; 
x_1143 = lean_ctor_get(x_1142, 1);
lean_inc(x_1143);
lean_dec(x_1142);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1144 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1143);
if (lean_obj_tag(x_1144) == 0)
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_1144, 1);
lean_inc(x_1146);
lean_dec(x_1144);
x_1128 = x_1145;
x_1129 = x_1146;
goto block_1141;
}
else
{
uint8_t x_1147; 
lean_dec(x_1124);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1147 = !lean_is_exclusive(x_1144);
if (x_1147 == 0)
{
return x_1144;
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
x_1148 = lean_ctor_get(x_1144, 0);
x_1149 = lean_ctor_get(x_1144, 1);
lean_inc(x_1149);
lean_inc(x_1148);
lean_dec(x_1144);
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
lean_dec(x_1124);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1151 = !lean_is_exclusive(x_1142);
if (x_1151 == 0)
{
return x_1142;
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1152 = lean_ctor_get(x_1142, 0);
x_1153 = lean_ctor_get(x_1142, 1);
lean_inc(x_1153);
lean_inc(x_1152);
lean_dec(x_1142);
x_1154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set(x_1154, 1, x_1153);
return x_1154;
}
}
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1155 = lean_array_get_size(x_23);
x_1156 = l_Array_toSubarray___rarg(x_23, x_27, x_1155);
x_1157 = l_Array_ofSubarray___rarg(x_1156);
lean_dec(x_1156);
lean_ctor_set_tag(x_1040, 4);
lean_ctor_set(x_1040, 1, x_1157);
lean_ctor_set(x_1040, 0, x_1126);
x_1158 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1159 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1040, x_1158, x_6, x_7, x_8, x_9, x_1125);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; 
x_1160 = lean_ctor_get(x_1159, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1159, 1);
lean_inc(x_1161);
lean_dec(x_1159);
x_1162 = lean_ctor_get(x_1160, 0);
lean_inc(x_1162);
x_1163 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1162, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1161);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; lean_object* x_1165; 
x_1164 = lean_ctor_get(x_1163, 1);
lean_inc(x_1164);
lean_dec(x_1163);
lean_ctor_set(x_1035, 1, x_2);
lean_ctor_set(x_1035, 0, x_1160);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1165 = l_Lean_Compiler_LCNF_Simp_simp(x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1164);
if (lean_obj_tag(x_1165) == 0)
{
lean_object* x_1166; lean_object* x_1167; 
x_1166 = lean_ctor_get(x_1165, 0);
lean_inc(x_1166);
x_1167 = lean_ctor_get(x_1165, 1);
lean_inc(x_1167);
lean_dec(x_1165);
x_1128 = x_1166;
x_1129 = x_1167;
goto block_1141;
}
else
{
uint8_t x_1168; 
lean_dec(x_1124);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1168 = !lean_is_exclusive(x_1165);
if (x_1168 == 0)
{
return x_1165;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1169 = lean_ctor_get(x_1165, 0);
x_1170 = lean_ctor_get(x_1165, 1);
lean_inc(x_1170);
lean_inc(x_1169);
lean_dec(x_1165);
x_1171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1171, 0, x_1169);
lean_ctor_set(x_1171, 1, x_1170);
return x_1171;
}
}
}
else
{
uint8_t x_1172; 
lean_dec(x_1160);
lean_dec(x_1124);
lean_free_object(x_1035);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1172 = !lean_is_exclusive(x_1163);
if (x_1172 == 0)
{
return x_1163;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = lean_ctor_get(x_1163, 0);
x_1174 = lean_ctor_get(x_1163, 1);
lean_inc(x_1174);
lean_inc(x_1173);
lean_dec(x_1163);
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set(x_1175, 1, x_1174);
return x_1175;
}
}
}
else
{
uint8_t x_1176; 
lean_dec(x_1124);
lean_free_object(x_1035);
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
x_1176 = !lean_is_exclusive(x_1159);
if (x_1176 == 0)
{
return x_1159;
}
else
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; 
x_1177 = lean_ctor_get(x_1159, 0);
x_1178 = lean_ctor_get(x_1159, 1);
lean_inc(x_1178);
lean_inc(x_1177);
lean_dec(x_1159);
x_1179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1179, 0, x_1177);
lean_ctor_set(x_1179, 1, x_1178);
return x_1179;
}
}
}
block_1141:
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
x_1130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1130, 0, x_1124);
x_1131 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1132 = lean_array_push(x_1131, x_1130);
x_1133 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1132, x_1128, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1129);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1132);
x_1134 = !lean_is_exclusive(x_1133);
if (x_1134 == 0)
{
lean_object* x_1135; lean_object* x_1136; 
x_1135 = lean_ctor_get(x_1133, 0);
if (lean_is_scalar(x_22)) {
 x_1136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1136 = x_22;
}
lean_ctor_set(x_1136, 0, x_1135);
lean_ctor_set(x_1133, 0, x_1136);
return x_1133;
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
x_1137 = lean_ctor_get(x_1133, 0);
x_1138 = lean_ctor_get(x_1133, 1);
lean_inc(x_1138);
lean_inc(x_1137);
lean_dec(x_1133);
if (lean_is_scalar(x_22)) {
 x_1139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1139 = x_22;
}
lean_ctor_set(x_1139, 0, x_1137);
x_1140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1140, 0, x_1139);
lean_ctor_set(x_1140, 1, x_1138);
return x_1140;
}
}
}
else
{
uint8_t x_1180; 
lean_free_object(x_1040);
lean_free_object(x_1035);
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
x_1180 = !lean_is_exclusive(x_1123);
if (x_1180 == 0)
{
return x_1123;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1123, 0);
x_1182 = lean_ctor_get(x_1123, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1123);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
return x_1183;
}
}
}
else
{
uint8_t x_1184; 
lean_free_object(x_1040);
lean_free_object(x_1035);
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
x_1184 = !lean_is_exclusive(x_1120);
if (x_1184 == 0)
{
return x_1120;
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1120, 0);
x_1186 = lean_ctor_get(x_1120, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1120);
x_1187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set(x_1187, 1, x_1186);
return x_1187;
}
}
}
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; uint8_t x_1191; 
x_1188 = lean_ctor_get(x_1040, 0);
x_1189 = lean_ctor_get(x_1040, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1040);
lean_inc(x_1188);
x_1190 = l_Lean_Expr_headBeta(x_1188);
x_1191 = l_Lean_Expr_isForall(x_1190);
lean_dec(x_1190);
if (x_1191 == 0)
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; uint8_t x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1192 = l_Lean_Compiler_LCNF_mkAuxParam(x_1188, x_1026, x_6, x_7, x_8, x_9, x_1189);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1192, 1);
lean_inc(x_1194);
if (lean_is_exclusive(x_1192)) {
 lean_ctor_release(x_1192, 0);
 lean_ctor_release(x_1192, 1);
 x_1195 = x_1192;
} else {
 lean_dec_ref(x_1192);
 x_1195 = lean_box(0);
}
x_1196 = lean_ctor_get(x_1193, 0);
lean_inc(x_1196);
x_1197 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1197 == 0)
{
lean_object* x_1223; 
lean_free_object(x_1035);
lean_dec(x_27);
lean_dec(x_23);
x_1223 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1196, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1194);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; lean_object* x_1225; 
x_1224 = lean_ctor_get(x_1223, 1);
lean_inc(x_1224);
lean_dec(x_1223);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1225 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1224);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1225, 1);
lean_inc(x_1227);
lean_dec(x_1225);
x_1198 = x_1226;
x_1199 = x_1227;
goto block_1222;
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; 
lean_dec(x_1195);
lean_dec(x_1193);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1228 = lean_ctor_get(x_1225, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1225, 1);
lean_inc(x_1229);
if (lean_is_exclusive(x_1225)) {
 lean_ctor_release(x_1225, 0);
 lean_ctor_release(x_1225, 1);
 x_1230 = x_1225;
} else {
 lean_dec_ref(x_1225);
 x_1230 = lean_box(0);
}
if (lean_is_scalar(x_1230)) {
 x_1231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1231 = x_1230;
}
lean_ctor_set(x_1231, 0, x_1228);
lean_ctor_set(x_1231, 1, x_1229);
return x_1231;
}
}
else
{
lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1195);
lean_dec(x_1193);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1232 = lean_ctor_get(x_1223, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1223, 1);
lean_inc(x_1233);
if (lean_is_exclusive(x_1223)) {
 lean_ctor_release(x_1223, 0);
 lean_ctor_release(x_1223, 1);
 x_1234 = x_1223;
} else {
 lean_dec_ref(x_1223);
 x_1234 = lean_box(0);
}
if (lean_is_scalar(x_1234)) {
 x_1235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1235 = x_1234;
}
lean_ctor_set(x_1235, 0, x_1232);
lean_ctor_set(x_1235, 1, x_1233);
return x_1235;
}
}
else
{
lean_object* x_1236; lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1236 = lean_array_get_size(x_23);
x_1237 = l_Array_toSubarray___rarg(x_23, x_27, x_1236);
x_1238 = l_Array_ofSubarray___rarg(x_1237);
lean_dec(x_1237);
x_1239 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1239, 0, x_1196);
lean_ctor_set(x_1239, 1, x_1238);
x_1240 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1241 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1239, x_1240, x_6, x_7, x_8, x_9, x_1194);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 1);
lean_inc(x_1243);
lean_dec(x_1241);
x_1244 = lean_ctor_get(x_1242, 0);
lean_inc(x_1244);
x_1245 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1244, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1243);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_1245, 1);
lean_inc(x_1246);
lean_dec(x_1245);
lean_ctor_set(x_1035, 1, x_2);
lean_ctor_set(x_1035, 0, x_1242);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1247 = l_Lean_Compiler_LCNF_Simp_simp(x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1246);
if (lean_obj_tag(x_1247) == 0)
{
lean_object* x_1248; lean_object* x_1249; 
x_1248 = lean_ctor_get(x_1247, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
lean_dec(x_1247);
x_1198 = x_1248;
x_1199 = x_1249;
goto block_1222;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; 
lean_dec(x_1195);
lean_dec(x_1193);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1250 = lean_ctor_get(x_1247, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1247, 1);
lean_inc(x_1251);
if (lean_is_exclusive(x_1247)) {
 lean_ctor_release(x_1247, 0);
 lean_ctor_release(x_1247, 1);
 x_1252 = x_1247;
} else {
 lean_dec_ref(x_1247);
 x_1252 = lean_box(0);
}
if (lean_is_scalar(x_1252)) {
 x_1253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1253 = x_1252;
}
lean_ctor_set(x_1253, 0, x_1250);
lean_ctor_set(x_1253, 1, x_1251);
return x_1253;
}
}
else
{
lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1242);
lean_dec(x_1195);
lean_dec(x_1193);
lean_free_object(x_1035);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1254 = lean_ctor_get(x_1245, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1245, 1);
lean_inc(x_1255);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1256 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1256 = lean_box(0);
}
if (lean_is_scalar(x_1256)) {
 x_1257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1257 = x_1256;
}
lean_ctor_set(x_1257, 0, x_1254);
lean_ctor_set(x_1257, 1, x_1255);
return x_1257;
}
}
else
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; 
lean_dec(x_1195);
lean_dec(x_1193);
lean_free_object(x_1035);
lean_dec(x_1032);
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
x_1258 = lean_ctor_get(x_1241, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1241, 1);
lean_inc(x_1259);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 lean_ctor_release(x_1241, 1);
 x_1260 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1260 = lean_box(0);
}
if (lean_is_scalar(x_1260)) {
 x_1261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1261 = x_1260;
}
lean_ctor_set(x_1261, 0, x_1258);
lean_ctor_set(x_1261, 1, x_1259);
return x_1261;
}
}
block_1222:
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1200 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1201 = lean_array_push(x_1200, x_1193);
x_1202 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1203 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1201, x_1198, x_1202, x_6, x_7, x_8, x_9, x_1199);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_ctor_get(x_1203, 1);
lean_inc(x_1205);
lean_dec(x_1203);
lean_inc(x_1204);
x_1206 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1206, 0, x_1204);
lean_closure_set(x_1206, 1, x_1200);
x_1207 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1032, x_1206, x_6, x_7, x_8, x_9, x_1205);
if (lean_obj_tag(x_1207) == 0)
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1208 = lean_ctor_get(x_1207, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_1207, 1);
lean_inc(x_1209);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 lean_ctor_release(x_1207, 1);
 x_1210 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1210 = lean_box(0);
}
if (lean_is_scalar(x_1195)) {
 x_1211 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1211 = x_1195;
 lean_ctor_set_tag(x_1211, 2);
}
lean_ctor_set(x_1211, 0, x_1204);
lean_ctor_set(x_1211, 1, x_1208);
if (lean_is_scalar(x_22)) {
 x_1212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1212 = x_22;
}
lean_ctor_set(x_1212, 0, x_1211);
if (lean_is_scalar(x_1210)) {
 x_1213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1213 = x_1210;
}
lean_ctor_set(x_1213, 0, x_1212);
lean_ctor_set(x_1213, 1, x_1209);
return x_1213;
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1204);
lean_dec(x_1195);
lean_dec(x_22);
x_1214 = lean_ctor_get(x_1207, 0);
lean_inc(x_1214);
x_1215 = lean_ctor_get(x_1207, 1);
lean_inc(x_1215);
if (lean_is_exclusive(x_1207)) {
 lean_ctor_release(x_1207, 0);
 lean_ctor_release(x_1207, 1);
 x_1216 = x_1207;
} else {
 lean_dec_ref(x_1207);
 x_1216 = lean_box(0);
}
if (lean_is_scalar(x_1216)) {
 x_1217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1217 = x_1216;
}
lean_ctor_set(x_1217, 0, x_1214);
lean_ctor_set(x_1217, 1, x_1215);
return x_1217;
}
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_1195);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1218 = lean_ctor_get(x_1203, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1203, 1);
lean_inc(x_1219);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 lean_ctor_release(x_1203, 1);
 x_1220 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1220 = lean_box(0);
}
if (lean_is_scalar(x_1220)) {
 x_1221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1221 = x_1220;
}
lean_ctor_set(x_1221, 0, x_1218);
lean_ctor_set(x_1221, 1, x_1219);
return x_1221;
}
}
}
else
{
lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
lean_dec(x_1188);
x_1262 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1263 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1264 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1262, x_1032, x_1263, x_6, x_7, x_8, x_9, x_1189);
if (lean_obj_tag(x_1264) == 0)
{
lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1265 = lean_ctor_get(x_1264, 0);
lean_inc(x_1265);
x_1266 = lean_ctor_get(x_1264, 1);
lean_inc(x_1266);
lean_dec(x_1264);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1267 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1265, x_6, x_7, x_8, x_9, x_1266);
if (lean_obj_tag(x_1267) == 0)
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; uint8_t x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1267, 1);
lean_inc(x_1269);
lean_dec(x_1267);
x_1270 = lean_ctor_get(x_1268, 0);
lean_inc(x_1270);
x_1271 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1271 == 0)
{
lean_object* x_1284; 
lean_free_object(x_1035);
lean_dec(x_27);
lean_dec(x_23);
x_1284 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1270, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1269);
if (lean_obj_tag(x_1284) == 0)
{
lean_object* x_1285; lean_object* x_1286; 
x_1285 = lean_ctor_get(x_1284, 1);
lean_inc(x_1285);
lean_dec(x_1284);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1286 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1285);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
x_1272 = x_1287;
x_1273 = x_1288;
goto block_1283;
}
else
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
lean_dec(x_1268);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1289 = lean_ctor_get(x_1286, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1286, 1);
lean_inc(x_1290);
if (lean_is_exclusive(x_1286)) {
 lean_ctor_release(x_1286, 0);
 lean_ctor_release(x_1286, 1);
 x_1291 = x_1286;
} else {
 lean_dec_ref(x_1286);
 x_1291 = lean_box(0);
}
if (lean_is_scalar(x_1291)) {
 x_1292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1292 = x_1291;
}
lean_ctor_set(x_1292, 0, x_1289);
lean_ctor_set(x_1292, 1, x_1290);
return x_1292;
}
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
lean_dec(x_1268);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1293 = lean_ctor_get(x_1284, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1284, 1);
lean_inc(x_1294);
if (lean_is_exclusive(x_1284)) {
 lean_ctor_release(x_1284, 0);
 lean_ctor_release(x_1284, 1);
 x_1295 = x_1284;
} else {
 lean_dec_ref(x_1284);
 x_1295 = lean_box(0);
}
if (lean_is_scalar(x_1295)) {
 x_1296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1296 = x_1295;
}
lean_ctor_set(x_1296, 0, x_1293);
lean_ctor_set(x_1296, 1, x_1294);
return x_1296;
}
}
else
{
lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
x_1297 = lean_array_get_size(x_23);
x_1298 = l_Array_toSubarray___rarg(x_23, x_27, x_1297);
x_1299 = l_Array_ofSubarray___rarg(x_1298);
lean_dec(x_1298);
x_1300 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1300, 0, x_1270);
lean_ctor_set(x_1300, 1, x_1299);
x_1301 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1302 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1300, x_1301, x_6, x_7, x_8, x_9, x_1269);
if (lean_obj_tag(x_1302) == 0)
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec(x_1302);
x_1305 = lean_ctor_get(x_1303, 0);
lean_inc(x_1305);
x_1306 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1305, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1304);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; 
x_1307 = lean_ctor_get(x_1306, 1);
lean_inc(x_1307);
lean_dec(x_1306);
lean_ctor_set(x_1035, 1, x_2);
lean_ctor_set(x_1035, 0, x_1303);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1308 = l_Lean_Compiler_LCNF_Simp_simp(x_1035, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1307);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; 
x_1309 = lean_ctor_get(x_1308, 0);
lean_inc(x_1309);
x_1310 = lean_ctor_get(x_1308, 1);
lean_inc(x_1310);
lean_dec(x_1308);
x_1272 = x_1309;
x_1273 = x_1310;
goto block_1283;
}
else
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
lean_dec(x_1268);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1311 = lean_ctor_get(x_1308, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1308, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1308)) {
 lean_ctor_release(x_1308, 0);
 lean_ctor_release(x_1308, 1);
 x_1313 = x_1308;
} else {
 lean_dec_ref(x_1308);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1313)) {
 x_1314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1314 = x_1313;
}
lean_ctor_set(x_1314, 0, x_1311);
lean_ctor_set(x_1314, 1, x_1312);
return x_1314;
}
}
else
{
lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; 
lean_dec(x_1303);
lean_dec(x_1268);
lean_free_object(x_1035);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1315 = lean_ctor_get(x_1306, 0);
lean_inc(x_1315);
x_1316 = lean_ctor_get(x_1306, 1);
lean_inc(x_1316);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 lean_ctor_release(x_1306, 1);
 x_1317 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1317 = lean_box(0);
}
if (lean_is_scalar(x_1317)) {
 x_1318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1318 = x_1317;
}
lean_ctor_set(x_1318, 0, x_1315);
lean_ctor_set(x_1318, 1, x_1316);
return x_1318;
}
}
else
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; 
lean_dec(x_1268);
lean_free_object(x_1035);
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
x_1319 = lean_ctor_get(x_1302, 0);
lean_inc(x_1319);
x_1320 = lean_ctor_get(x_1302, 1);
lean_inc(x_1320);
if (lean_is_exclusive(x_1302)) {
 lean_ctor_release(x_1302, 0);
 lean_ctor_release(x_1302, 1);
 x_1321 = x_1302;
} else {
 lean_dec_ref(x_1302);
 x_1321 = lean_box(0);
}
if (lean_is_scalar(x_1321)) {
 x_1322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1322 = x_1321;
}
lean_ctor_set(x_1322, 0, x_1319);
lean_ctor_set(x_1322, 1, x_1320);
return x_1322;
}
}
block_1283:
{
lean_object* x_1274; lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1274, 0, x_1268);
x_1275 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1276 = lean_array_push(x_1275, x_1274);
x_1277 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1276, x_1272, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1273);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1276);
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
if (lean_is_exclusive(x_1277)) {
 lean_ctor_release(x_1277, 0);
 lean_ctor_release(x_1277, 1);
 x_1280 = x_1277;
} else {
 lean_dec_ref(x_1277);
 x_1280 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1281 = x_22;
}
lean_ctor_set(x_1281, 0, x_1278);
if (lean_is_scalar(x_1280)) {
 x_1282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1282 = x_1280;
}
lean_ctor_set(x_1282, 0, x_1281);
lean_ctor_set(x_1282, 1, x_1279);
return x_1282;
}
}
else
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; 
lean_free_object(x_1035);
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
x_1323 = lean_ctor_get(x_1267, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1267, 1);
lean_inc(x_1324);
if (lean_is_exclusive(x_1267)) {
 lean_ctor_release(x_1267, 0);
 lean_ctor_release(x_1267, 1);
 x_1325 = x_1267;
} else {
 lean_dec_ref(x_1267);
 x_1325 = lean_box(0);
}
if (lean_is_scalar(x_1325)) {
 x_1326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1326 = x_1325;
}
lean_ctor_set(x_1326, 0, x_1323);
lean_ctor_set(x_1326, 1, x_1324);
return x_1326;
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
lean_free_object(x_1035);
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
x_1327 = lean_ctor_get(x_1264, 0);
lean_inc(x_1327);
x_1328 = lean_ctor_get(x_1264, 1);
lean_inc(x_1328);
if (lean_is_exclusive(x_1264)) {
 lean_ctor_release(x_1264, 0);
 lean_ctor_release(x_1264, 1);
 x_1329 = x_1264;
} else {
 lean_dec_ref(x_1264);
 x_1329 = lean_box(0);
}
if (lean_is_scalar(x_1329)) {
 x_1330 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1330 = x_1329;
}
lean_ctor_set(x_1330, 0, x_1327);
lean_ctor_set(x_1330, 1, x_1328);
return x_1330;
}
}
}
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; 
x_1331 = lean_ctor_get(x_1035, 1);
lean_inc(x_1331);
lean_dec(x_1035);
x_1332 = lean_ctor_get(x_21, 2);
lean_inc(x_1332);
lean_dec(x_21);
x_1333 = l_Lean_Compiler_LCNF_inferAppType(x_1332, x_33, x_6, x_7, x_8, x_9, x_1331);
x_1334 = lean_ctor_get(x_1333, 0);
lean_inc(x_1334);
x_1335 = lean_ctor_get(x_1333, 1);
lean_inc(x_1335);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 lean_ctor_release(x_1333, 1);
 x_1336 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1336 = lean_box(0);
}
lean_inc(x_1334);
x_1337 = l_Lean_Expr_headBeta(x_1334);
x_1338 = l_Lean_Expr_isForall(x_1337);
lean_dec(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; uint8_t x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1339 = l_Lean_Compiler_LCNF_mkAuxParam(x_1334, x_1026, x_6, x_7, x_8, x_9, x_1335);
x_1340 = lean_ctor_get(x_1339, 0);
lean_inc(x_1340);
x_1341 = lean_ctor_get(x_1339, 1);
lean_inc(x_1341);
if (lean_is_exclusive(x_1339)) {
 lean_ctor_release(x_1339, 0);
 lean_ctor_release(x_1339, 1);
 x_1342 = x_1339;
} else {
 lean_dec_ref(x_1339);
 x_1342 = lean_box(0);
}
x_1343 = lean_ctor_get(x_1340, 0);
lean_inc(x_1343);
x_1344 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1344 == 0)
{
lean_object* x_1370; 
lean_dec(x_1336);
lean_dec(x_27);
lean_dec(x_23);
x_1370 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1343, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1341);
if (lean_obj_tag(x_1370) == 0)
{
lean_object* x_1371; lean_object* x_1372; 
x_1371 = lean_ctor_get(x_1370, 1);
lean_inc(x_1371);
lean_dec(x_1370);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1372 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1371);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1372, 1);
lean_inc(x_1374);
lean_dec(x_1372);
x_1345 = x_1373;
x_1346 = x_1374;
goto block_1369;
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
lean_dec(x_1342);
lean_dec(x_1340);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1375 = lean_ctor_get(x_1372, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1372, 1);
lean_inc(x_1376);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 lean_ctor_release(x_1372, 1);
 x_1377 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1377 = lean_box(0);
}
if (lean_is_scalar(x_1377)) {
 x_1378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1378 = x_1377;
}
lean_ctor_set(x_1378, 0, x_1375);
lean_ctor_set(x_1378, 1, x_1376);
return x_1378;
}
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; 
lean_dec(x_1342);
lean_dec(x_1340);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1379 = lean_ctor_get(x_1370, 0);
lean_inc(x_1379);
x_1380 = lean_ctor_get(x_1370, 1);
lean_inc(x_1380);
if (lean_is_exclusive(x_1370)) {
 lean_ctor_release(x_1370, 0);
 lean_ctor_release(x_1370, 1);
 x_1381 = x_1370;
} else {
 lean_dec_ref(x_1370);
 x_1381 = lean_box(0);
}
if (lean_is_scalar(x_1381)) {
 x_1382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1382 = x_1381;
}
lean_ctor_set(x_1382, 0, x_1379);
lean_ctor_set(x_1382, 1, x_1380);
return x_1382;
}
}
else
{
lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1383 = lean_array_get_size(x_23);
x_1384 = l_Array_toSubarray___rarg(x_23, x_27, x_1383);
x_1385 = l_Array_ofSubarray___rarg(x_1384);
lean_dec(x_1384);
if (lean_is_scalar(x_1336)) {
 x_1386 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1386 = x_1336;
 lean_ctor_set_tag(x_1386, 4);
}
lean_ctor_set(x_1386, 0, x_1343);
lean_ctor_set(x_1386, 1, x_1385);
x_1387 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1388 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1386, x_1387, x_6, x_7, x_8, x_9, x_1341);
if (lean_obj_tag(x_1388) == 0)
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1389 = lean_ctor_get(x_1388, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1388, 1);
lean_inc(x_1390);
lean_dec(x_1388);
x_1391 = lean_ctor_get(x_1389, 0);
lean_inc(x_1391);
x_1392 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1391, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1390);
if (lean_obj_tag(x_1392) == 0)
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; 
x_1393 = lean_ctor_get(x_1392, 1);
lean_inc(x_1393);
lean_dec(x_1392);
x_1394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1394, 0, x_1389);
lean_ctor_set(x_1394, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1395 = l_Lean_Compiler_LCNF_Simp_simp(x_1394, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1393);
if (lean_obj_tag(x_1395) == 0)
{
lean_object* x_1396; lean_object* x_1397; 
x_1396 = lean_ctor_get(x_1395, 0);
lean_inc(x_1396);
x_1397 = lean_ctor_get(x_1395, 1);
lean_inc(x_1397);
lean_dec(x_1395);
x_1345 = x_1396;
x_1346 = x_1397;
goto block_1369;
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1342);
lean_dec(x_1340);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1398 = lean_ctor_get(x_1395, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1395, 1);
lean_inc(x_1399);
if (lean_is_exclusive(x_1395)) {
 lean_ctor_release(x_1395, 0);
 lean_ctor_release(x_1395, 1);
 x_1400 = x_1395;
} else {
 lean_dec_ref(x_1395);
 x_1400 = lean_box(0);
}
if (lean_is_scalar(x_1400)) {
 x_1401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1401 = x_1400;
}
lean_ctor_set(x_1401, 0, x_1398);
lean_ctor_set(x_1401, 1, x_1399);
return x_1401;
}
}
else
{
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; 
lean_dec(x_1389);
lean_dec(x_1342);
lean_dec(x_1340);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1402 = lean_ctor_get(x_1392, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1392, 1);
lean_inc(x_1403);
if (lean_is_exclusive(x_1392)) {
 lean_ctor_release(x_1392, 0);
 lean_ctor_release(x_1392, 1);
 x_1404 = x_1392;
} else {
 lean_dec_ref(x_1392);
 x_1404 = lean_box(0);
}
if (lean_is_scalar(x_1404)) {
 x_1405 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1405 = x_1404;
}
lean_ctor_set(x_1405, 0, x_1402);
lean_ctor_set(x_1405, 1, x_1403);
return x_1405;
}
}
else
{
lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
lean_dec(x_1342);
lean_dec(x_1340);
lean_dec(x_1032);
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
x_1406 = lean_ctor_get(x_1388, 0);
lean_inc(x_1406);
x_1407 = lean_ctor_get(x_1388, 1);
lean_inc(x_1407);
if (lean_is_exclusive(x_1388)) {
 lean_ctor_release(x_1388, 0);
 lean_ctor_release(x_1388, 1);
 x_1408 = x_1388;
} else {
 lean_dec_ref(x_1388);
 x_1408 = lean_box(0);
}
if (lean_is_scalar(x_1408)) {
 x_1409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1409 = x_1408;
}
lean_ctor_set(x_1409, 0, x_1406);
lean_ctor_set(x_1409, 1, x_1407);
return x_1409;
}
}
block_1369:
{
lean_object* x_1347; lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1347 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1348 = lean_array_push(x_1347, x_1340);
x_1349 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1350 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1348, x_1345, x_1349, x_6, x_7, x_8, x_9, x_1346);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
lean_dec(x_1350);
lean_inc(x_1351);
x_1353 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1353, 0, x_1351);
lean_closure_set(x_1353, 1, x_1347);
x_1354 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1032, x_1353, x_6, x_7, x_8, x_9, x_1352);
if (lean_obj_tag(x_1354) == 0)
{
lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
x_1355 = lean_ctor_get(x_1354, 0);
lean_inc(x_1355);
x_1356 = lean_ctor_get(x_1354, 1);
lean_inc(x_1356);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1357 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1357 = lean_box(0);
}
if (lean_is_scalar(x_1342)) {
 x_1358 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1358 = x_1342;
 lean_ctor_set_tag(x_1358, 2);
}
lean_ctor_set(x_1358, 0, x_1351);
lean_ctor_set(x_1358, 1, x_1355);
if (lean_is_scalar(x_22)) {
 x_1359 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1359 = x_22;
}
lean_ctor_set(x_1359, 0, x_1358);
if (lean_is_scalar(x_1357)) {
 x_1360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1360 = x_1357;
}
lean_ctor_set(x_1360, 0, x_1359);
lean_ctor_set(x_1360, 1, x_1356);
return x_1360;
}
else
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; 
lean_dec(x_1351);
lean_dec(x_1342);
lean_dec(x_22);
x_1361 = lean_ctor_get(x_1354, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_1354, 1);
lean_inc(x_1362);
if (lean_is_exclusive(x_1354)) {
 lean_ctor_release(x_1354, 0);
 lean_ctor_release(x_1354, 1);
 x_1363 = x_1354;
} else {
 lean_dec_ref(x_1354);
 x_1363 = lean_box(0);
}
if (lean_is_scalar(x_1363)) {
 x_1364 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1364 = x_1363;
}
lean_ctor_set(x_1364, 0, x_1361);
lean_ctor_set(x_1364, 1, x_1362);
return x_1364;
}
}
else
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; 
lean_dec(x_1342);
lean_dec(x_1032);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1365 = lean_ctor_get(x_1350, 0);
lean_inc(x_1365);
x_1366 = lean_ctor_get(x_1350, 1);
lean_inc(x_1366);
if (lean_is_exclusive(x_1350)) {
 lean_ctor_release(x_1350, 0);
 lean_ctor_release(x_1350, 1);
 x_1367 = x_1350;
} else {
 lean_dec_ref(x_1350);
 x_1367 = lean_box(0);
}
if (lean_is_scalar(x_1367)) {
 x_1368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1368 = x_1367;
}
lean_ctor_set(x_1368, 0, x_1365);
lean_ctor_set(x_1368, 1, x_1366);
return x_1368;
}
}
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
lean_dec(x_1334);
x_1410 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1411 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1412 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1410, x_1032, x_1411, x_6, x_7, x_8, x_9, x_1335);
if (lean_obj_tag(x_1412) == 0)
{
lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1413 = lean_ctor_get(x_1412, 0);
lean_inc(x_1413);
x_1414 = lean_ctor_get(x_1412, 1);
lean_inc(x_1414);
lean_dec(x_1412);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1415 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1413, x_6, x_7, x_8, x_9, x_1414);
if (lean_obj_tag(x_1415) == 0)
{
lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; uint8_t x_1419; lean_object* x_1420; lean_object* x_1421; 
x_1416 = lean_ctor_get(x_1415, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1415, 1);
lean_inc(x_1417);
lean_dec(x_1415);
x_1418 = lean_ctor_get(x_1416, 0);
lean_inc(x_1418);
x_1419 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1419 == 0)
{
lean_object* x_1432; 
lean_dec(x_1336);
lean_dec(x_27);
lean_dec(x_23);
x_1432 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1418, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1417);
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
x_1420 = x_1435;
x_1421 = x_1436;
goto block_1431;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_1416);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1437 = lean_ctor_get(x_1434, 0);
lean_inc(x_1437);
x_1438 = lean_ctor_get(x_1434, 1);
lean_inc(x_1438);
if (lean_is_exclusive(x_1434)) {
 lean_ctor_release(x_1434, 0);
 lean_ctor_release(x_1434, 1);
 x_1439 = x_1434;
} else {
 lean_dec_ref(x_1434);
 x_1439 = lean_box(0);
}
if (lean_is_scalar(x_1439)) {
 x_1440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1440 = x_1439;
}
lean_ctor_set(x_1440, 0, x_1437);
lean_ctor_set(x_1440, 1, x_1438);
return x_1440;
}
}
else
{
lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; 
lean_dec(x_1416);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1441 = lean_ctor_get(x_1432, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1432, 1);
lean_inc(x_1442);
if (lean_is_exclusive(x_1432)) {
 lean_ctor_release(x_1432, 0);
 lean_ctor_release(x_1432, 1);
 x_1443 = x_1432;
} else {
 lean_dec_ref(x_1432);
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
}
else
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; 
x_1445 = lean_array_get_size(x_23);
x_1446 = l_Array_toSubarray___rarg(x_23, x_27, x_1445);
x_1447 = l_Array_ofSubarray___rarg(x_1446);
lean_dec(x_1446);
if (lean_is_scalar(x_1336)) {
 x_1448 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1448 = x_1336;
 lean_ctor_set_tag(x_1448, 4);
}
lean_ctor_set(x_1448, 0, x_1418);
lean_ctor_set(x_1448, 1, x_1447);
x_1449 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1450 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1448, x_1449, x_6, x_7, x_8, x_9, x_1417);
if (lean_obj_tag(x_1450) == 0)
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1451 = lean_ctor_get(x_1450, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1450, 1);
lean_inc(x_1452);
lean_dec(x_1450);
x_1453 = lean_ctor_get(x_1451, 0);
lean_inc(x_1453);
x_1454 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1453, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1452);
if (lean_obj_tag(x_1454) == 0)
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1455 = lean_ctor_get(x_1454, 1);
lean_inc(x_1455);
lean_dec(x_1454);
x_1456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1456, 0, x_1451);
lean_ctor_set(x_1456, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1457 = l_Lean_Compiler_LCNF_Simp_simp(x_1456, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1455);
if (lean_obj_tag(x_1457) == 0)
{
lean_object* x_1458; lean_object* x_1459; 
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_ctor_get(x_1457, 1);
lean_inc(x_1459);
lean_dec(x_1457);
x_1420 = x_1458;
x_1421 = x_1459;
goto block_1431;
}
else
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_1416);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1460 = lean_ctor_get(x_1457, 0);
lean_inc(x_1460);
x_1461 = lean_ctor_get(x_1457, 1);
lean_inc(x_1461);
if (lean_is_exclusive(x_1457)) {
 lean_ctor_release(x_1457, 0);
 lean_ctor_release(x_1457, 1);
 x_1462 = x_1457;
} else {
 lean_dec_ref(x_1457);
 x_1462 = lean_box(0);
}
if (lean_is_scalar(x_1462)) {
 x_1463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1463 = x_1462;
}
lean_ctor_set(x_1463, 0, x_1460);
lean_ctor_set(x_1463, 1, x_1461);
return x_1463;
}
}
else
{
lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
lean_dec(x_1451);
lean_dec(x_1416);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1464 = lean_ctor_get(x_1454, 0);
lean_inc(x_1464);
x_1465 = lean_ctor_get(x_1454, 1);
lean_inc(x_1465);
if (lean_is_exclusive(x_1454)) {
 lean_ctor_release(x_1454, 0);
 lean_ctor_release(x_1454, 1);
 x_1466 = x_1454;
} else {
 lean_dec_ref(x_1454);
 x_1466 = lean_box(0);
}
if (lean_is_scalar(x_1466)) {
 x_1467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1467 = x_1466;
}
lean_ctor_set(x_1467, 0, x_1464);
lean_ctor_set(x_1467, 1, x_1465);
return x_1467;
}
}
else
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; 
lean_dec(x_1416);
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
x_1468 = lean_ctor_get(x_1450, 0);
lean_inc(x_1468);
x_1469 = lean_ctor_get(x_1450, 1);
lean_inc(x_1469);
if (lean_is_exclusive(x_1450)) {
 lean_ctor_release(x_1450, 0);
 lean_ctor_release(x_1450, 1);
 x_1470 = x_1450;
} else {
 lean_dec_ref(x_1450);
 x_1470 = lean_box(0);
}
if (lean_is_scalar(x_1470)) {
 x_1471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1471 = x_1470;
}
lean_ctor_set(x_1471, 0, x_1468);
lean_ctor_set(x_1471, 1, x_1469);
return x_1471;
}
}
block_1431:
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1422 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1422, 0, x_1416);
x_1423 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1424 = lean_array_push(x_1423, x_1422);
x_1425 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1424, x_1420, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1421);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1424);
x_1426 = lean_ctor_get(x_1425, 0);
lean_inc(x_1426);
x_1427 = lean_ctor_get(x_1425, 1);
lean_inc(x_1427);
if (lean_is_exclusive(x_1425)) {
 lean_ctor_release(x_1425, 0);
 lean_ctor_release(x_1425, 1);
 x_1428 = x_1425;
} else {
 lean_dec_ref(x_1425);
 x_1428 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1429 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1429 = x_22;
}
lean_ctor_set(x_1429, 0, x_1426);
if (lean_is_scalar(x_1428)) {
 x_1430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1430 = x_1428;
}
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_1427);
return x_1430;
}
}
else
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; 
lean_dec(x_1336);
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
x_1472 = lean_ctor_get(x_1415, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1415, 1);
lean_inc(x_1473);
if (lean_is_exclusive(x_1415)) {
 lean_ctor_release(x_1415, 0);
 lean_ctor_release(x_1415, 1);
 x_1474 = x_1415;
} else {
 lean_dec_ref(x_1415);
 x_1474 = lean_box(0);
}
if (lean_is_scalar(x_1474)) {
 x_1475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1475 = x_1474;
}
lean_ctor_set(x_1475, 0, x_1472);
lean_ctor_set(x_1475, 1, x_1473);
return x_1475;
}
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; 
lean_dec(x_1336);
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
x_1476 = lean_ctor_get(x_1412, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1412, 1);
lean_inc(x_1477);
if (lean_is_exclusive(x_1412)) {
 lean_ctor_release(x_1412, 0);
 lean_ctor_release(x_1412, 1);
 x_1478 = x_1412;
} else {
 lean_dec_ref(x_1412);
 x_1478 = lean_box(0);
}
if (lean_is_scalar(x_1478)) {
 x_1479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1479 = x_1478;
}
lean_ctor_set(x_1479, 0, x_1476);
lean_ctor_set(x_1479, 1, x_1477);
return x_1479;
}
}
}
}
else
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; 
lean_dec(x_33);
lean_dec(x_21);
x_1480 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1033);
x_1481 = lean_ctor_get(x_1480, 1);
lean_inc(x_1481);
lean_dec(x_1480);
x_1482 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_1482, 0, x_3);
lean_closure_set(x_1482, 1, x_4);
lean_closure_set(x_1482, 2, x_5);
lean_closure_set(x_1482, 3, x_27);
lean_closure_set(x_1482, 4, x_24);
lean_closure_set(x_1482, 5, x_26);
lean_closure_set(x_1482, 6, x_2);
lean_closure_set(x_1482, 7, x_23);
x_1483 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1032, x_1482, x_6, x_7, x_8, x_9, x_1481);
if (lean_obj_tag(x_1483) == 0)
{
uint8_t x_1484; 
x_1484 = !lean_is_exclusive(x_1483);
if (x_1484 == 0)
{
lean_object* x_1485; lean_object* x_1486; 
x_1485 = lean_ctor_get(x_1483, 0);
if (lean_is_scalar(x_22)) {
 x_1486 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1486 = x_22;
}
lean_ctor_set(x_1486, 0, x_1485);
lean_ctor_set(x_1483, 0, x_1486);
return x_1483;
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; 
x_1487 = lean_ctor_get(x_1483, 0);
x_1488 = lean_ctor_get(x_1483, 1);
lean_inc(x_1488);
lean_inc(x_1487);
lean_dec(x_1483);
if (lean_is_scalar(x_22)) {
 x_1489 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1489 = x_22;
}
lean_ctor_set(x_1489, 0, x_1487);
x_1490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1490, 0, x_1489);
lean_ctor_set(x_1490, 1, x_1488);
return x_1490;
}
}
else
{
uint8_t x_1491; 
lean_dec(x_22);
x_1491 = !lean_is_exclusive(x_1483);
if (x_1491 == 0)
{
return x_1483;
}
else
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1492 = lean_ctor_get(x_1483, 0);
x_1493 = lean_ctor_get(x_1483, 1);
lean_inc(x_1493);
lean_inc(x_1492);
lean_dec(x_1483);
x_1494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1494, 0, x_1492);
lean_ctor_set(x_1494, 1, x_1493);
return x_1494;
}
}
}
}
else
{
uint8_t x_1495; 
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
x_1495 = !lean_is_exclusive(x_1031);
if (x_1495 == 0)
{
return x_1031;
}
else
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1496 = lean_ctor_get(x_1031, 0);
x_1497 = lean_ctor_get(x_1031, 1);
lean_inc(x_1497);
lean_inc(x_1496);
lean_dec(x_1031);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
return x_1498;
}
}
}
}
else
{
uint8_t x_1518; 
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
x_1518 = !lean_is_exclusive(x_1027);
if (x_1518 == 0)
{
return x_1027;
}
else
{
lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
x_1519 = lean_ctor_get(x_1027, 0);
x_1520 = lean_ctor_get(x_1027, 1);
lean_inc(x_1520);
lean_inc(x_1519);
lean_dec(x_1027);
x_1521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1521, 0, x_1519);
lean_ctor_set(x_1521, 1, x_1520);
return x_1521;
}
}
}
case 3:
{
lean_object* x_1522; lean_object* x_1523; 
x_1522 = lean_ctor_get(x_11, 0);
lean_inc(x_1522);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_1522);
x_1523 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_1522, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1523) == 0)
{
lean_object* x_1524; lean_object* x_1525; uint8_t x_1526; 
x_1524 = lean_ctor_get(x_1523, 0);
lean_inc(x_1524);
x_1525 = lean_ctor_get(x_1523, 1);
lean_inc(x_1525);
lean_dec(x_1523);
x_1526 = !lean_is_exclusive(x_3);
if (x_1526 == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; uint8_t x_1531; lean_object* x_1532; 
x_1527 = lean_ctor_get(x_3, 2);
x_1528 = lean_ctor_get(x_3, 3);
lean_inc(x_1522);
x_1529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1529, 0, x_1522);
lean_ctor_set(x_1529, 1, x_1527);
x_1530 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_1528, x_1522, x_1524);
lean_ctor_set(x_3, 3, x_1530);
lean_ctor_set(x_3, 2, x_1529);
x_1531 = 0;
lean_inc(x_33);
x_1532 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1531, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1525);
lean_dec(x_29);
if (lean_obj_tag(x_1532) == 0)
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_2005; 
x_1533 = lean_ctor_get(x_1532, 0);
lean_inc(x_1533);
x_1534 = lean_ctor_get(x_1532, 1);
lean_inc(x_1534);
lean_dec(x_1532);
x_2005 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2005 == 0)
{
lean_object* x_2006; 
x_2006 = lean_box(0);
x_1535 = x_2006;
goto block_2004;
}
else
{
uint8_t x_2007; 
x_2007 = lean_nat_dec_eq(x_24, x_27);
if (x_2007 == 0)
{
lean_object* x_2008; 
x_2008 = lean_box(0);
x_1535 = x_2008;
goto block_2004;
}
else
{
lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_2009 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1534);
x_2010 = lean_ctor_get(x_2009, 1);
lean_inc(x_2010);
lean_dec(x_2009);
x_2011 = l_Lean_Compiler_LCNF_Simp_simp(x_1533, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2010);
if (lean_obj_tag(x_2011) == 0)
{
uint8_t x_2012; 
x_2012 = !lean_is_exclusive(x_2011);
if (x_2012 == 0)
{
lean_object* x_2013; lean_object* x_2014; 
x_2013 = lean_ctor_get(x_2011, 0);
x_2014 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2014, 0, x_2013);
lean_ctor_set(x_2011, 0, x_2014);
return x_2011;
}
else
{
lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; 
x_2015 = lean_ctor_get(x_2011, 0);
x_2016 = lean_ctor_get(x_2011, 1);
lean_inc(x_2016);
lean_inc(x_2015);
lean_dec(x_2011);
x_2017 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2017, 0, x_2015);
x_2018 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2018, 0, x_2017);
lean_ctor_set(x_2018, 1, x_2016);
return x_2018;
}
}
else
{
uint8_t x_2019; 
x_2019 = !lean_is_exclusive(x_2011);
if (x_2019 == 0)
{
return x_2011;
}
else
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
x_2020 = lean_ctor_get(x_2011, 0);
x_2021 = lean_ctor_get(x_2011, 1);
lean_inc(x_2021);
lean_inc(x_2020);
lean_dec(x_2011);
x_2022 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2022, 0, x_2020);
lean_ctor_set(x_2022, 1, x_2021);
return x_2022;
}
}
}
}
block_2004:
{
lean_object* x_1536; 
lean_dec(x_1535);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1536 = l_Lean_Compiler_LCNF_Simp_simp(x_1533, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1534);
if (lean_obj_tag(x_1536) == 0)
{
lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; 
x_1537 = lean_ctor_get(x_1536, 0);
lean_inc(x_1537);
x_1538 = lean_ctor_get(x_1536, 1);
lean_inc(x_1538);
lean_dec(x_1536);
lean_inc(x_1537);
x_1539 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1537);
if (x_1539 == 0)
{
lean_object* x_1540; uint8_t x_1541; 
x_1540 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1538);
x_1541 = !lean_is_exclusive(x_1540);
if (x_1541 == 0)
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; uint8_t x_1546; 
x_1542 = lean_ctor_get(x_1540, 1);
x_1543 = lean_ctor_get(x_1540, 0);
lean_dec(x_1543);
x_1544 = lean_ctor_get(x_21, 2);
lean_inc(x_1544);
lean_dec(x_21);
x_1545 = l_Lean_Compiler_LCNF_inferAppType(x_1544, x_33, x_6, x_7, x_8, x_9, x_1542);
x_1546 = !lean_is_exclusive(x_1545);
if (x_1546 == 0)
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; uint8_t x_1550; 
x_1547 = lean_ctor_get(x_1545, 0);
x_1548 = lean_ctor_get(x_1545, 1);
lean_inc(x_1547);
x_1549 = l_Lean_Expr_headBeta(x_1547);
x_1550 = l_Lean_Expr_isForall(x_1549);
lean_dec(x_1549);
if (x_1550 == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; uint8_t x_1556; lean_object* x_1557; lean_object* x_1558; 
x_1551 = l_Lean_Compiler_LCNF_mkAuxParam(x_1547, x_1531, x_6, x_7, x_8, x_9, x_1548);
x_1552 = lean_ctor_get(x_1551, 0);
lean_inc(x_1552);
x_1553 = lean_ctor_get(x_1551, 1);
lean_inc(x_1553);
if (lean_is_exclusive(x_1551)) {
 lean_ctor_release(x_1551, 0);
 lean_ctor_release(x_1551, 1);
 x_1554 = x_1551;
} else {
 lean_dec_ref(x_1551);
 x_1554 = lean_box(0);
}
x_1555 = lean_ctor_get(x_1552, 0);
lean_inc(x_1555);
x_1556 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1556 == 0)
{
lean_object* x_1585; 
lean_free_object(x_1545);
lean_free_object(x_1540);
lean_dec(x_27);
lean_dec(x_23);
x_1585 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1555, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1553);
if (lean_obj_tag(x_1585) == 0)
{
lean_object* x_1586; lean_object* x_1587; 
x_1586 = lean_ctor_get(x_1585, 1);
lean_inc(x_1586);
lean_dec(x_1585);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1587 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1586);
if (lean_obj_tag(x_1587) == 0)
{
lean_object* x_1588; lean_object* x_1589; 
x_1588 = lean_ctor_get(x_1587, 0);
lean_inc(x_1588);
x_1589 = lean_ctor_get(x_1587, 1);
lean_inc(x_1589);
lean_dec(x_1587);
x_1557 = x_1588;
x_1558 = x_1589;
goto block_1584;
}
else
{
uint8_t x_1590; 
lean_dec(x_1554);
lean_dec(x_1552);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1590 = !lean_is_exclusive(x_1587);
if (x_1590 == 0)
{
return x_1587;
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; 
x_1591 = lean_ctor_get(x_1587, 0);
x_1592 = lean_ctor_get(x_1587, 1);
lean_inc(x_1592);
lean_inc(x_1591);
lean_dec(x_1587);
x_1593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1593, 0, x_1591);
lean_ctor_set(x_1593, 1, x_1592);
return x_1593;
}
}
}
else
{
uint8_t x_1594; 
lean_dec(x_1554);
lean_dec(x_1552);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1594 = !lean_is_exclusive(x_1585);
if (x_1594 == 0)
{
return x_1585;
}
else
{
lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; 
x_1595 = lean_ctor_get(x_1585, 0);
x_1596 = lean_ctor_get(x_1585, 1);
lean_inc(x_1596);
lean_inc(x_1595);
lean_dec(x_1585);
x_1597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1597, 0, x_1595);
lean_ctor_set(x_1597, 1, x_1596);
return x_1597;
}
}
}
else
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
x_1598 = lean_array_get_size(x_23);
x_1599 = l_Array_toSubarray___rarg(x_23, x_27, x_1598);
x_1600 = l_Array_ofSubarray___rarg(x_1599);
lean_dec(x_1599);
lean_ctor_set_tag(x_1545, 4);
lean_ctor_set(x_1545, 1, x_1600);
lean_ctor_set(x_1545, 0, x_1555);
x_1601 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1602 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1545, x_1601, x_6, x_7, x_8, x_9, x_1553);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; 
x_1603 = lean_ctor_get(x_1602, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1602, 1);
lean_inc(x_1604);
lean_dec(x_1602);
x_1605 = lean_ctor_get(x_1603, 0);
lean_inc(x_1605);
x_1606 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1605, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1604);
if (lean_obj_tag(x_1606) == 0)
{
lean_object* x_1607; lean_object* x_1608; 
x_1607 = lean_ctor_get(x_1606, 1);
lean_inc(x_1607);
lean_dec(x_1606);
lean_ctor_set(x_1540, 1, x_2);
lean_ctor_set(x_1540, 0, x_1603);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1608 = l_Lean_Compiler_LCNF_Simp_simp(x_1540, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1607);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; 
x_1609 = lean_ctor_get(x_1608, 0);
lean_inc(x_1609);
x_1610 = lean_ctor_get(x_1608, 1);
lean_inc(x_1610);
lean_dec(x_1608);
x_1557 = x_1609;
x_1558 = x_1610;
goto block_1584;
}
else
{
uint8_t x_1611; 
lean_dec(x_1554);
lean_dec(x_1552);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1611 = !lean_is_exclusive(x_1608);
if (x_1611 == 0)
{
return x_1608;
}
else
{
lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; 
x_1612 = lean_ctor_get(x_1608, 0);
x_1613 = lean_ctor_get(x_1608, 1);
lean_inc(x_1613);
lean_inc(x_1612);
lean_dec(x_1608);
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
lean_dec(x_1603);
lean_dec(x_1554);
lean_dec(x_1552);
lean_free_object(x_1540);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1615 = !lean_is_exclusive(x_1606);
if (x_1615 == 0)
{
return x_1606;
}
else
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
x_1616 = lean_ctor_get(x_1606, 0);
x_1617 = lean_ctor_get(x_1606, 1);
lean_inc(x_1617);
lean_inc(x_1616);
lean_dec(x_1606);
x_1618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1618, 0, x_1616);
lean_ctor_set(x_1618, 1, x_1617);
return x_1618;
}
}
}
else
{
uint8_t x_1619; 
lean_dec(x_1554);
lean_dec(x_1552);
lean_free_object(x_1540);
lean_dec(x_1537);
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
x_1619 = !lean_is_exclusive(x_1602);
if (x_1619 == 0)
{
return x_1602;
}
else
{
lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1620 = lean_ctor_get(x_1602, 0);
x_1621 = lean_ctor_get(x_1602, 1);
lean_inc(x_1621);
lean_inc(x_1620);
lean_dec(x_1602);
x_1622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1622, 0, x_1620);
lean_ctor_set(x_1622, 1, x_1621);
return x_1622;
}
}
}
block_1584:
{
lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
x_1559 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1560 = lean_array_push(x_1559, x_1552);
x_1561 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1562 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1560, x_1557, x_1561, x_6, x_7, x_8, x_9, x_1558);
if (lean_obj_tag(x_1562) == 0)
{
lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; 
x_1563 = lean_ctor_get(x_1562, 0);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1562, 1);
lean_inc(x_1564);
lean_dec(x_1562);
lean_inc(x_1563);
x_1565 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1565, 0, x_1563);
lean_closure_set(x_1565, 1, x_1559);
x_1566 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1537, x_1565, x_6, x_7, x_8, x_9, x_1564);
if (lean_obj_tag(x_1566) == 0)
{
uint8_t x_1567; 
x_1567 = !lean_is_exclusive(x_1566);
if (x_1567 == 0)
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
x_1568 = lean_ctor_get(x_1566, 0);
if (lean_is_scalar(x_1554)) {
 x_1569 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1569 = x_1554;
 lean_ctor_set_tag(x_1569, 2);
}
lean_ctor_set(x_1569, 0, x_1563);
lean_ctor_set(x_1569, 1, x_1568);
if (lean_is_scalar(x_22)) {
 x_1570 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1570 = x_22;
}
lean_ctor_set(x_1570, 0, x_1569);
lean_ctor_set(x_1566, 0, x_1570);
return x_1566;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; 
x_1571 = lean_ctor_get(x_1566, 0);
x_1572 = lean_ctor_get(x_1566, 1);
lean_inc(x_1572);
lean_inc(x_1571);
lean_dec(x_1566);
if (lean_is_scalar(x_1554)) {
 x_1573 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1573 = x_1554;
 lean_ctor_set_tag(x_1573, 2);
}
lean_ctor_set(x_1573, 0, x_1563);
lean_ctor_set(x_1573, 1, x_1571);
if (lean_is_scalar(x_22)) {
 x_1574 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1574 = x_22;
}
lean_ctor_set(x_1574, 0, x_1573);
x_1575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1575, 0, x_1574);
lean_ctor_set(x_1575, 1, x_1572);
return x_1575;
}
}
else
{
uint8_t x_1576; 
lean_dec(x_1563);
lean_dec(x_1554);
lean_dec(x_22);
x_1576 = !lean_is_exclusive(x_1566);
if (x_1576 == 0)
{
return x_1566;
}
else
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
x_1577 = lean_ctor_get(x_1566, 0);
x_1578 = lean_ctor_get(x_1566, 1);
lean_inc(x_1578);
lean_inc(x_1577);
lean_dec(x_1566);
x_1579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1579, 0, x_1577);
lean_ctor_set(x_1579, 1, x_1578);
return x_1579;
}
}
}
else
{
uint8_t x_1580; 
lean_dec(x_1554);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1580 = !lean_is_exclusive(x_1562);
if (x_1580 == 0)
{
return x_1562;
}
else
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1581 = lean_ctor_get(x_1562, 0);
x_1582 = lean_ctor_get(x_1562, 1);
lean_inc(x_1582);
lean_inc(x_1581);
lean_dec(x_1562);
x_1583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1583, 0, x_1581);
lean_ctor_set(x_1583, 1, x_1582);
return x_1583;
}
}
}
}
else
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
lean_dec(x_1547);
x_1623 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1624 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1625 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1623, x_1537, x_1624, x_6, x_7, x_8, x_9, x_1548);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; 
x_1626 = lean_ctor_get(x_1625, 0);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1625, 1);
lean_inc(x_1627);
lean_dec(x_1625);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1628 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1626, x_6, x_7, x_8, x_9, x_1627);
if (lean_obj_tag(x_1628) == 0)
{
lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; uint8_t x_1632; lean_object* x_1633; lean_object* x_1634; 
x_1629 = lean_ctor_get(x_1628, 0);
lean_inc(x_1629);
x_1630 = lean_ctor_get(x_1628, 1);
lean_inc(x_1630);
lean_dec(x_1628);
x_1631 = lean_ctor_get(x_1629, 0);
lean_inc(x_1631);
x_1632 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1632 == 0)
{
lean_object* x_1647; 
lean_free_object(x_1545);
lean_free_object(x_1540);
lean_dec(x_27);
lean_dec(x_23);
x_1647 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1631, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1630);
if (lean_obj_tag(x_1647) == 0)
{
lean_object* x_1648; lean_object* x_1649; 
x_1648 = lean_ctor_get(x_1647, 1);
lean_inc(x_1648);
lean_dec(x_1647);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1649 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1648);
if (lean_obj_tag(x_1649) == 0)
{
lean_object* x_1650; lean_object* x_1651; 
x_1650 = lean_ctor_get(x_1649, 0);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_1649, 1);
lean_inc(x_1651);
lean_dec(x_1649);
x_1633 = x_1650;
x_1634 = x_1651;
goto block_1646;
}
else
{
uint8_t x_1652; 
lean_dec(x_1629);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1652 = !lean_is_exclusive(x_1649);
if (x_1652 == 0)
{
return x_1649;
}
else
{
lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1653 = lean_ctor_get(x_1649, 0);
x_1654 = lean_ctor_get(x_1649, 1);
lean_inc(x_1654);
lean_inc(x_1653);
lean_dec(x_1649);
x_1655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1655, 0, x_1653);
lean_ctor_set(x_1655, 1, x_1654);
return x_1655;
}
}
}
else
{
uint8_t x_1656; 
lean_dec(x_1629);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1656 = !lean_is_exclusive(x_1647);
if (x_1656 == 0)
{
return x_1647;
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
x_1657 = lean_ctor_get(x_1647, 0);
x_1658 = lean_ctor_get(x_1647, 1);
lean_inc(x_1658);
lean_inc(x_1657);
lean_dec(x_1647);
x_1659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1659, 0, x_1657);
lean_ctor_set(x_1659, 1, x_1658);
return x_1659;
}
}
}
else
{
lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; 
x_1660 = lean_array_get_size(x_23);
x_1661 = l_Array_toSubarray___rarg(x_23, x_27, x_1660);
x_1662 = l_Array_ofSubarray___rarg(x_1661);
lean_dec(x_1661);
lean_ctor_set_tag(x_1545, 4);
lean_ctor_set(x_1545, 1, x_1662);
lean_ctor_set(x_1545, 0, x_1631);
x_1663 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1664 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1545, x_1663, x_6, x_7, x_8, x_9, x_1630);
if (lean_obj_tag(x_1664) == 0)
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
x_1665 = lean_ctor_get(x_1664, 0);
lean_inc(x_1665);
x_1666 = lean_ctor_get(x_1664, 1);
lean_inc(x_1666);
lean_dec(x_1664);
x_1667 = lean_ctor_get(x_1665, 0);
lean_inc(x_1667);
x_1668 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1667, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1666);
if (lean_obj_tag(x_1668) == 0)
{
lean_object* x_1669; lean_object* x_1670; 
x_1669 = lean_ctor_get(x_1668, 1);
lean_inc(x_1669);
lean_dec(x_1668);
lean_ctor_set(x_1540, 1, x_2);
lean_ctor_set(x_1540, 0, x_1665);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1670 = l_Lean_Compiler_LCNF_Simp_simp(x_1540, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1669);
if (lean_obj_tag(x_1670) == 0)
{
lean_object* x_1671; lean_object* x_1672; 
x_1671 = lean_ctor_get(x_1670, 0);
lean_inc(x_1671);
x_1672 = lean_ctor_get(x_1670, 1);
lean_inc(x_1672);
lean_dec(x_1670);
x_1633 = x_1671;
x_1634 = x_1672;
goto block_1646;
}
else
{
uint8_t x_1673; 
lean_dec(x_1629);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1673 = !lean_is_exclusive(x_1670);
if (x_1673 == 0)
{
return x_1670;
}
else
{
lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; 
x_1674 = lean_ctor_get(x_1670, 0);
x_1675 = lean_ctor_get(x_1670, 1);
lean_inc(x_1675);
lean_inc(x_1674);
lean_dec(x_1670);
x_1676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1676, 0, x_1674);
lean_ctor_set(x_1676, 1, x_1675);
return x_1676;
}
}
}
else
{
uint8_t x_1677; 
lean_dec(x_1665);
lean_dec(x_1629);
lean_free_object(x_1540);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1677 = !lean_is_exclusive(x_1668);
if (x_1677 == 0)
{
return x_1668;
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; 
x_1678 = lean_ctor_get(x_1668, 0);
x_1679 = lean_ctor_get(x_1668, 1);
lean_inc(x_1679);
lean_inc(x_1678);
lean_dec(x_1668);
x_1680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1680, 0, x_1678);
lean_ctor_set(x_1680, 1, x_1679);
return x_1680;
}
}
}
else
{
uint8_t x_1681; 
lean_dec(x_1629);
lean_free_object(x_1540);
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
x_1681 = !lean_is_exclusive(x_1664);
if (x_1681 == 0)
{
return x_1664;
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; 
x_1682 = lean_ctor_get(x_1664, 0);
x_1683 = lean_ctor_get(x_1664, 1);
lean_inc(x_1683);
lean_inc(x_1682);
lean_dec(x_1664);
x_1684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1684, 0, x_1682);
lean_ctor_set(x_1684, 1, x_1683);
return x_1684;
}
}
}
block_1646:
{
lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; uint8_t x_1639; 
x_1635 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1635, 0, x_1629);
x_1636 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1637 = lean_array_push(x_1636, x_1635);
x_1638 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1637, x_1633, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1634);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1637);
x_1639 = !lean_is_exclusive(x_1638);
if (x_1639 == 0)
{
lean_object* x_1640; lean_object* x_1641; 
x_1640 = lean_ctor_get(x_1638, 0);
if (lean_is_scalar(x_22)) {
 x_1641 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1641 = x_22;
}
lean_ctor_set(x_1641, 0, x_1640);
lean_ctor_set(x_1638, 0, x_1641);
return x_1638;
}
else
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; 
x_1642 = lean_ctor_get(x_1638, 0);
x_1643 = lean_ctor_get(x_1638, 1);
lean_inc(x_1643);
lean_inc(x_1642);
lean_dec(x_1638);
if (lean_is_scalar(x_22)) {
 x_1644 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1644 = x_22;
}
lean_ctor_set(x_1644, 0, x_1642);
x_1645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1645, 0, x_1644);
lean_ctor_set(x_1645, 1, x_1643);
return x_1645;
}
}
}
else
{
uint8_t x_1685; 
lean_free_object(x_1545);
lean_free_object(x_1540);
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
x_1685 = !lean_is_exclusive(x_1628);
if (x_1685 == 0)
{
return x_1628;
}
else
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
x_1686 = lean_ctor_get(x_1628, 0);
x_1687 = lean_ctor_get(x_1628, 1);
lean_inc(x_1687);
lean_inc(x_1686);
lean_dec(x_1628);
x_1688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1688, 0, x_1686);
lean_ctor_set(x_1688, 1, x_1687);
return x_1688;
}
}
}
else
{
uint8_t x_1689; 
lean_free_object(x_1545);
lean_free_object(x_1540);
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
x_1689 = !lean_is_exclusive(x_1625);
if (x_1689 == 0)
{
return x_1625;
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; 
x_1690 = lean_ctor_get(x_1625, 0);
x_1691 = lean_ctor_get(x_1625, 1);
lean_inc(x_1691);
lean_inc(x_1690);
lean_dec(x_1625);
x_1692 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1692, 0, x_1690);
lean_ctor_set(x_1692, 1, x_1691);
return x_1692;
}
}
}
}
else
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; uint8_t x_1696; 
x_1693 = lean_ctor_get(x_1545, 0);
x_1694 = lean_ctor_get(x_1545, 1);
lean_inc(x_1694);
lean_inc(x_1693);
lean_dec(x_1545);
lean_inc(x_1693);
x_1695 = l_Lean_Expr_headBeta(x_1693);
x_1696 = l_Lean_Expr_isForall(x_1695);
lean_dec(x_1695);
if (x_1696 == 0)
{
lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; uint8_t x_1702; lean_object* x_1703; lean_object* x_1704; 
x_1697 = l_Lean_Compiler_LCNF_mkAuxParam(x_1693, x_1531, x_6, x_7, x_8, x_9, x_1694);
x_1698 = lean_ctor_get(x_1697, 0);
lean_inc(x_1698);
x_1699 = lean_ctor_get(x_1697, 1);
lean_inc(x_1699);
if (lean_is_exclusive(x_1697)) {
 lean_ctor_release(x_1697, 0);
 lean_ctor_release(x_1697, 1);
 x_1700 = x_1697;
} else {
 lean_dec_ref(x_1697);
 x_1700 = lean_box(0);
}
x_1701 = lean_ctor_get(x_1698, 0);
lean_inc(x_1701);
x_1702 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1702 == 0)
{
lean_object* x_1728; 
lean_free_object(x_1540);
lean_dec(x_27);
lean_dec(x_23);
x_1728 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1701, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1699);
if (lean_obj_tag(x_1728) == 0)
{
lean_object* x_1729; lean_object* x_1730; 
x_1729 = lean_ctor_get(x_1728, 1);
lean_inc(x_1729);
lean_dec(x_1728);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1730 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1729);
if (lean_obj_tag(x_1730) == 0)
{
lean_object* x_1731; lean_object* x_1732; 
x_1731 = lean_ctor_get(x_1730, 0);
lean_inc(x_1731);
x_1732 = lean_ctor_get(x_1730, 1);
lean_inc(x_1732);
lean_dec(x_1730);
x_1703 = x_1731;
x_1704 = x_1732;
goto block_1727;
}
else
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; 
lean_dec(x_1700);
lean_dec(x_1698);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1733 = lean_ctor_get(x_1730, 0);
lean_inc(x_1733);
x_1734 = lean_ctor_get(x_1730, 1);
lean_inc(x_1734);
if (lean_is_exclusive(x_1730)) {
 lean_ctor_release(x_1730, 0);
 lean_ctor_release(x_1730, 1);
 x_1735 = x_1730;
} else {
 lean_dec_ref(x_1730);
 x_1735 = lean_box(0);
}
if (lean_is_scalar(x_1735)) {
 x_1736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1736 = x_1735;
}
lean_ctor_set(x_1736, 0, x_1733);
lean_ctor_set(x_1736, 1, x_1734);
return x_1736;
}
}
else
{
lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
lean_dec(x_1700);
lean_dec(x_1698);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1737 = lean_ctor_get(x_1728, 0);
lean_inc(x_1737);
x_1738 = lean_ctor_get(x_1728, 1);
lean_inc(x_1738);
if (lean_is_exclusive(x_1728)) {
 lean_ctor_release(x_1728, 0);
 lean_ctor_release(x_1728, 1);
 x_1739 = x_1728;
} else {
 lean_dec_ref(x_1728);
 x_1739 = lean_box(0);
}
if (lean_is_scalar(x_1739)) {
 x_1740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1740 = x_1739;
}
lean_ctor_set(x_1740, 0, x_1737);
lean_ctor_set(x_1740, 1, x_1738);
return x_1740;
}
}
else
{
lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1741 = lean_array_get_size(x_23);
x_1742 = l_Array_toSubarray___rarg(x_23, x_27, x_1741);
x_1743 = l_Array_ofSubarray___rarg(x_1742);
lean_dec(x_1742);
x_1744 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1744, 0, x_1701);
lean_ctor_set(x_1744, 1, x_1743);
x_1745 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1746 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1744, x_1745, x_6, x_7, x_8, x_9, x_1699);
if (lean_obj_tag(x_1746) == 0)
{
lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
x_1747 = lean_ctor_get(x_1746, 0);
lean_inc(x_1747);
x_1748 = lean_ctor_get(x_1746, 1);
lean_inc(x_1748);
lean_dec(x_1746);
x_1749 = lean_ctor_get(x_1747, 0);
lean_inc(x_1749);
x_1750 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1749, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1748);
if (lean_obj_tag(x_1750) == 0)
{
lean_object* x_1751; lean_object* x_1752; 
x_1751 = lean_ctor_get(x_1750, 1);
lean_inc(x_1751);
lean_dec(x_1750);
lean_ctor_set(x_1540, 1, x_2);
lean_ctor_set(x_1540, 0, x_1747);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1752 = l_Lean_Compiler_LCNF_Simp_simp(x_1540, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1751);
if (lean_obj_tag(x_1752) == 0)
{
lean_object* x_1753; lean_object* x_1754; 
x_1753 = lean_ctor_get(x_1752, 0);
lean_inc(x_1753);
x_1754 = lean_ctor_get(x_1752, 1);
lean_inc(x_1754);
lean_dec(x_1752);
x_1703 = x_1753;
x_1704 = x_1754;
goto block_1727;
}
else
{
lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; 
lean_dec(x_1700);
lean_dec(x_1698);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1755 = lean_ctor_get(x_1752, 0);
lean_inc(x_1755);
x_1756 = lean_ctor_get(x_1752, 1);
lean_inc(x_1756);
if (lean_is_exclusive(x_1752)) {
 lean_ctor_release(x_1752, 0);
 lean_ctor_release(x_1752, 1);
 x_1757 = x_1752;
} else {
 lean_dec_ref(x_1752);
 x_1757 = lean_box(0);
}
if (lean_is_scalar(x_1757)) {
 x_1758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1758 = x_1757;
}
lean_ctor_set(x_1758, 0, x_1755);
lean_ctor_set(x_1758, 1, x_1756);
return x_1758;
}
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
lean_dec(x_1747);
lean_dec(x_1700);
lean_dec(x_1698);
lean_free_object(x_1540);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1759 = lean_ctor_get(x_1750, 0);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1750, 1);
lean_inc(x_1760);
if (lean_is_exclusive(x_1750)) {
 lean_ctor_release(x_1750, 0);
 lean_ctor_release(x_1750, 1);
 x_1761 = x_1750;
} else {
 lean_dec_ref(x_1750);
 x_1761 = lean_box(0);
}
if (lean_is_scalar(x_1761)) {
 x_1762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1762 = x_1761;
}
lean_ctor_set(x_1762, 0, x_1759);
lean_ctor_set(x_1762, 1, x_1760);
return x_1762;
}
}
else
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
lean_dec(x_1700);
lean_dec(x_1698);
lean_free_object(x_1540);
lean_dec(x_1537);
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
x_1763 = lean_ctor_get(x_1746, 0);
lean_inc(x_1763);
x_1764 = lean_ctor_get(x_1746, 1);
lean_inc(x_1764);
if (lean_is_exclusive(x_1746)) {
 lean_ctor_release(x_1746, 0);
 lean_ctor_release(x_1746, 1);
 x_1765 = x_1746;
} else {
 lean_dec_ref(x_1746);
 x_1765 = lean_box(0);
}
if (lean_is_scalar(x_1765)) {
 x_1766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1766 = x_1765;
}
lean_ctor_set(x_1766, 0, x_1763);
lean_ctor_set(x_1766, 1, x_1764);
return x_1766;
}
}
block_1727:
{
lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; 
x_1705 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1706 = lean_array_push(x_1705, x_1698);
x_1707 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1708 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1706, x_1703, x_1707, x_6, x_7, x_8, x_9, x_1704);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; 
x_1709 = lean_ctor_get(x_1708, 0);
lean_inc(x_1709);
x_1710 = lean_ctor_get(x_1708, 1);
lean_inc(x_1710);
lean_dec(x_1708);
lean_inc(x_1709);
x_1711 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1711, 0, x_1709);
lean_closure_set(x_1711, 1, x_1705);
x_1712 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1537, x_1711, x_6, x_7, x_8, x_9, x_1710);
if (lean_obj_tag(x_1712) == 0)
{
lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; 
x_1713 = lean_ctor_get(x_1712, 0);
lean_inc(x_1713);
x_1714 = lean_ctor_get(x_1712, 1);
lean_inc(x_1714);
if (lean_is_exclusive(x_1712)) {
 lean_ctor_release(x_1712, 0);
 lean_ctor_release(x_1712, 1);
 x_1715 = x_1712;
} else {
 lean_dec_ref(x_1712);
 x_1715 = lean_box(0);
}
if (lean_is_scalar(x_1700)) {
 x_1716 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1716 = x_1700;
 lean_ctor_set_tag(x_1716, 2);
}
lean_ctor_set(x_1716, 0, x_1709);
lean_ctor_set(x_1716, 1, x_1713);
if (lean_is_scalar(x_22)) {
 x_1717 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1717 = x_22;
}
lean_ctor_set(x_1717, 0, x_1716);
if (lean_is_scalar(x_1715)) {
 x_1718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1718 = x_1715;
}
lean_ctor_set(x_1718, 0, x_1717);
lean_ctor_set(x_1718, 1, x_1714);
return x_1718;
}
else
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; 
lean_dec(x_1709);
lean_dec(x_1700);
lean_dec(x_22);
x_1719 = lean_ctor_get(x_1712, 0);
lean_inc(x_1719);
x_1720 = lean_ctor_get(x_1712, 1);
lean_inc(x_1720);
if (lean_is_exclusive(x_1712)) {
 lean_ctor_release(x_1712, 0);
 lean_ctor_release(x_1712, 1);
 x_1721 = x_1712;
} else {
 lean_dec_ref(x_1712);
 x_1721 = lean_box(0);
}
if (lean_is_scalar(x_1721)) {
 x_1722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1722 = x_1721;
}
lean_ctor_set(x_1722, 0, x_1719);
lean_ctor_set(x_1722, 1, x_1720);
return x_1722;
}
}
else
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; 
lean_dec(x_1700);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1723 = lean_ctor_get(x_1708, 0);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1708, 1);
lean_inc(x_1724);
if (lean_is_exclusive(x_1708)) {
 lean_ctor_release(x_1708, 0);
 lean_ctor_release(x_1708, 1);
 x_1725 = x_1708;
} else {
 lean_dec_ref(x_1708);
 x_1725 = lean_box(0);
}
if (lean_is_scalar(x_1725)) {
 x_1726 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1726 = x_1725;
}
lean_ctor_set(x_1726, 0, x_1723);
lean_ctor_set(x_1726, 1, x_1724);
return x_1726;
}
}
}
else
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; 
lean_dec(x_1693);
x_1767 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1768 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1769 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1767, x_1537, x_1768, x_6, x_7, x_8, x_9, x_1694);
if (lean_obj_tag(x_1769) == 0)
{
lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; 
x_1770 = lean_ctor_get(x_1769, 0);
lean_inc(x_1770);
x_1771 = lean_ctor_get(x_1769, 1);
lean_inc(x_1771);
lean_dec(x_1769);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1772 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1770, x_6, x_7, x_8, x_9, x_1771);
if (lean_obj_tag(x_1772) == 0)
{
lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; uint8_t x_1776; lean_object* x_1777; lean_object* x_1778; 
x_1773 = lean_ctor_get(x_1772, 0);
lean_inc(x_1773);
x_1774 = lean_ctor_get(x_1772, 1);
lean_inc(x_1774);
lean_dec(x_1772);
x_1775 = lean_ctor_get(x_1773, 0);
lean_inc(x_1775);
x_1776 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1776 == 0)
{
lean_object* x_1789; 
lean_free_object(x_1540);
lean_dec(x_27);
lean_dec(x_23);
x_1789 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1775, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1774);
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
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1791 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1790);
if (lean_obj_tag(x_1791) == 0)
{
lean_object* x_1792; lean_object* x_1793; 
x_1792 = lean_ctor_get(x_1791, 0);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1791, 1);
lean_inc(x_1793);
lean_dec(x_1791);
x_1777 = x_1792;
x_1778 = x_1793;
goto block_1788;
}
else
{
lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; 
lean_dec(x_1773);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1794 = lean_ctor_get(x_1791, 0);
lean_inc(x_1794);
x_1795 = lean_ctor_get(x_1791, 1);
lean_inc(x_1795);
if (lean_is_exclusive(x_1791)) {
 lean_ctor_release(x_1791, 0);
 lean_ctor_release(x_1791, 1);
 x_1796 = x_1791;
} else {
 lean_dec_ref(x_1791);
 x_1796 = lean_box(0);
}
if (lean_is_scalar(x_1796)) {
 x_1797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1797 = x_1796;
}
lean_ctor_set(x_1797, 0, x_1794);
lean_ctor_set(x_1797, 1, x_1795);
return x_1797;
}
}
else
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
lean_dec(x_1773);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1798 = lean_ctor_get(x_1789, 0);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1789, 1);
lean_inc(x_1799);
if (lean_is_exclusive(x_1789)) {
 lean_ctor_release(x_1789, 0);
 lean_ctor_release(x_1789, 1);
 x_1800 = x_1789;
} else {
 lean_dec_ref(x_1789);
 x_1800 = lean_box(0);
}
if (lean_is_scalar(x_1800)) {
 x_1801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1801 = x_1800;
}
lean_ctor_set(x_1801, 0, x_1798);
lean_ctor_set(x_1801, 1, x_1799);
return x_1801;
}
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; 
x_1802 = lean_array_get_size(x_23);
x_1803 = l_Array_toSubarray___rarg(x_23, x_27, x_1802);
x_1804 = l_Array_ofSubarray___rarg(x_1803);
lean_dec(x_1803);
x_1805 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1805, 0, x_1775);
lean_ctor_set(x_1805, 1, x_1804);
x_1806 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1807 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1805, x_1806, x_6, x_7, x_8, x_9, x_1774);
if (lean_obj_tag(x_1807) == 0)
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; 
x_1808 = lean_ctor_get(x_1807, 0);
lean_inc(x_1808);
x_1809 = lean_ctor_get(x_1807, 1);
lean_inc(x_1809);
lean_dec(x_1807);
x_1810 = lean_ctor_get(x_1808, 0);
lean_inc(x_1810);
x_1811 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1810, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1809);
if (lean_obj_tag(x_1811) == 0)
{
lean_object* x_1812; lean_object* x_1813; 
x_1812 = lean_ctor_get(x_1811, 1);
lean_inc(x_1812);
lean_dec(x_1811);
lean_ctor_set(x_1540, 1, x_2);
lean_ctor_set(x_1540, 0, x_1808);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1813 = l_Lean_Compiler_LCNF_Simp_simp(x_1540, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1812);
if (lean_obj_tag(x_1813) == 0)
{
lean_object* x_1814; lean_object* x_1815; 
x_1814 = lean_ctor_get(x_1813, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1813, 1);
lean_inc(x_1815);
lean_dec(x_1813);
x_1777 = x_1814;
x_1778 = x_1815;
goto block_1788;
}
else
{
lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; 
lean_dec(x_1773);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1816 = lean_ctor_get(x_1813, 0);
lean_inc(x_1816);
x_1817 = lean_ctor_get(x_1813, 1);
lean_inc(x_1817);
if (lean_is_exclusive(x_1813)) {
 lean_ctor_release(x_1813, 0);
 lean_ctor_release(x_1813, 1);
 x_1818 = x_1813;
} else {
 lean_dec_ref(x_1813);
 x_1818 = lean_box(0);
}
if (lean_is_scalar(x_1818)) {
 x_1819 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1819 = x_1818;
}
lean_ctor_set(x_1819, 0, x_1816);
lean_ctor_set(x_1819, 1, x_1817);
return x_1819;
}
}
else
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
lean_dec(x_1808);
lean_dec(x_1773);
lean_free_object(x_1540);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1820 = lean_ctor_get(x_1811, 0);
lean_inc(x_1820);
x_1821 = lean_ctor_get(x_1811, 1);
lean_inc(x_1821);
if (lean_is_exclusive(x_1811)) {
 lean_ctor_release(x_1811, 0);
 lean_ctor_release(x_1811, 1);
 x_1822 = x_1811;
} else {
 lean_dec_ref(x_1811);
 x_1822 = lean_box(0);
}
if (lean_is_scalar(x_1822)) {
 x_1823 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1823 = x_1822;
}
lean_ctor_set(x_1823, 0, x_1820);
lean_ctor_set(x_1823, 1, x_1821);
return x_1823;
}
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; 
lean_dec(x_1773);
lean_free_object(x_1540);
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
x_1824 = lean_ctor_get(x_1807, 0);
lean_inc(x_1824);
x_1825 = lean_ctor_get(x_1807, 1);
lean_inc(x_1825);
if (lean_is_exclusive(x_1807)) {
 lean_ctor_release(x_1807, 0);
 lean_ctor_release(x_1807, 1);
 x_1826 = x_1807;
} else {
 lean_dec_ref(x_1807);
 x_1826 = lean_box(0);
}
if (lean_is_scalar(x_1826)) {
 x_1827 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1827 = x_1826;
}
lean_ctor_set(x_1827, 0, x_1824);
lean_ctor_set(x_1827, 1, x_1825);
return x_1827;
}
}
block_1788:
{
lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; 
x_1779 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1779, 0, x_1773);
x_1780 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1781 = lean_array_push(x_1780, x_1779);
x_1782 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1781, x_1777, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1778);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1781);
x_1783 = lean_ctor_get(x_1782, 0);
lean_inc(x_1783);
x_1784 = lean_ctor_get(x_1782, 1);
lean_inc(x_1784);
if (lean_is_exclusive(x_1782)) {
 lean_ctor_release(x_1782, 0);
 lean_ctor_release(x_1782, 1);
 x_1785 = x_1782;
} else {
 lean_dec_ref(x_1782);
 x_1785 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1786 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1786 = x_22;
}
lean_ctor_set(x_1786, 0, x_1783);
if (lean_is_scalar(x_1785)) {
 x_1787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1787 = x_1785;
}
lean_ctor_set(x_1787, 0, x_1786);
lean_ctor_set(x_1787, 1, x_1784);
return x_1787;
}
}
else
{
lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; 
lean_free_object(x_1540);
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
x_1828 = lean_ctor_get(x_1772, 0);
lean_inc(x_1828);
x_1829 = lean_ctor_get(x_1772, 1);
lean_inc(x_1829);
if (lean_is_exclusive(x_1772)) {
 lean_ctor_release(x_1772, 0);
 lean_ctor_release(x_1772, 1);
 x_1830 = x_1772;
} else {
 lean_dec_ref(x_1772);
 x_1830 = lean_box(0);
}
if (lean_is_scalar(x_1830)) {
 x_1831 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1831 = x_1830;
}
lean_ctor_set(x_1831, 0, x_1828);
lean_ctor_set(x_1831, 1, x_1829);
return x_1831;
}
}
else
{
lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; 
lean_free_object(x_1540);
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
x_1832 = lean_ctor_get(x_1769, 0);
lean_inc(x_1832);
x_1833 = lean_ctor_get(x_1769, 1);
lean_inc(x_1833);
if (lean_is_exclusive(x_1769)) {
 lean_ctor_release(x_1769, 0);
 lean_ctor_release(x_1769, 1);
 x_1834 = x_1769;
} else {
 lean_dec_ref(x_1769);
 x_1834 = lean_box(0);
}
if (lean_is_scalar(x_1834)) {
 x_1835 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1835 = x_1834;
}
lean_ctor_set(x_1835, 0, x_1832);
lean_ctor_set(x_1835, 1, x_1833);
return x_1835;
}
}
}
}
else
{
lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; uint8_t x_1843; 
x_1836 = lean_ctor_get(x_1540, 1);
lean_inc(x_1836);
lean_dec(x_1540);
x_1837 = lean_ctor_get(x_21, 2);
lean_inc(x_1837);
lean_dec(x_21);
x_1838 = l_Lean_Compiler_LCNF_inferAppType(x_1837, x_33, x_6, x_7, x_8, x_9, x_1836);
x_1839 = lean_ctor_get(x_1838, 0);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1838, 1);
lean_inc(x_1840);
if (lean_is_exclusive(x_1838)) {
 lean_ctor_release(x_1838, 0);
 lean_ctor_release(x_1838, 1);
 x_1841 = x_1838;
} else {
 lean_dec_ref(x_1838);
 x_1841 = lean_box(0);
}
lean_inc(x_1839);
x_1842 = l_Lean_Expr_headBeta(x_1839);
x_1843 = l_Lean_Expr_isForall(x_1842);
lean_dec(x_1842);
if (x_1843 == 0)
{
lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; uint8_t x_1849; lean_object* x_1850; lean_object* x_1851; 
x_1844 = l_Lean_Compiler_LCNF_mkAuxParam(x_1839, x_1531, x_6, x_7, x_8, x_9, x_1840);
x_1845 = lean_ctor_get(x_1844, 0);
lean_inc(x_1845);
x_1846 = lean_ctor_get(x_1844, 1);
lean_inc(x_1846);
if (lean_is_exclusive(x_1844)) {
 lean_ctor_release(x_1844, 0);
 lean_ctor_release(x_1844, 1);
 x_1847 = x_1844;
} else {
 lean_dec_ref(x_1844);
 x_1847 = lean_box(0);
}
x_1848 = lean_ctor_get(x_1845, 0);
lean_inc(x_1848);
x_1849 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1849 == 0)
{
lean_object* x_1875; 
lean_dec(x_1841);
lean_dec(x_27);
lean_dec(x_23);
x_1875 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1848, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1846);
if (lean_obj_tag(x_1875) == 0)
{
lean_object* x_1876; lean_object* x_1877; 
x_1876 = lean_ctor_get(x_1875, 1);
lean_inc(x_1876);
lean_dec(x_1875);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1877 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1876);
if (lean_obj_tag(x_1877) == 0)
{
lean_object* x_1878; lean_object* x_1879; 
x_1878 = lean_ctor_get(x_1877, 0);
lean_inc(x_1878);
x_1879 = lean_ctor_get(x_1877, 1);
lean_inc(x_1879);
lean_dec(x_1877);
x_1850 = x_1878;
x_1851 = x_1879;
goto block_1874;
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; 
lean_dec(x_1847);
lean_dec(x_1845);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1880 = lean_ctor_get(x_1877, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1877, 1);
lean_inc(x_1881);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_1882 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_1882 = lean_box(0);
}
if (lean_is_scalar(x_1882)) {
 x_1883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1883 = x_1882;
}
lean_ctor_set(x_1883, 0, x_1880);
lean_ctor_set(x_1883, 1, x_1881);
return x_1883;
}
}
else
{
lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; 
lean_dec(x_1847);
lean_dec(x_1845);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1884 = lean_ctor_get(x_1875, 0);
lean_inc(x_1884);
x_1885 = lean_ctor_get(x_1875, 1);
lean_inc(x_1885);
if (lean_is_exclusive(x_1875)) {
 lean_ctor_release(x_1875, 0);
 lean_ctor_release(x_1875, 1);
 x_1886 = x_1875;
} else {
 lean_dec_ref(x_1875);
 x_1886 = lean_box(0);
}
if (lean_is_scalar(x_1886)) {
 x_1887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1887 = x_1886;
}
lean_ctor_set(x_1887, 0, x_1884);
lean_ctor_set(x_1887, 1, x_1885);
return x_1887;
}
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; 
x_1888 = lean_array_get_size(x_23);
x_1889 = l_Array_toSubarray___rarg(x_23, x_27, x_1888);
x_1890 = l_Array_ofSubarray___rarg(x_1889);
lean_dec(x_1889);
if (lean_is_scalar(x_1841)) {
 x_1891 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1891 = x_1841;
 lean_ctor_set_tag(x_1891, 4);
}
lean_ctor_set(x_1891, 0, x_1848);
lean_ctor_set(x_1891, 1, x_1890);
x_1892 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1893 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1891, x_1892, x_6, x_7, x_8, x_9, x_1846);
if (lean_obj_tag(x_1893) == 0)
{
lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; 
x_1894 = lean_ctor_get(x_1893, 0);
lean_inc(x_1894);
x_1895 = lean_ctor_get(x_1893, 1);
lean_inc(x_1895);
lean_dec(x_1893);
x_1896 = lean_ctor_get(x_1894, 0);
lean_inc(x_1896);
x_1897 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1896, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1895);
if (lean_obj_tag(x_1897) == 0)
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; 
x_1898 = lean_ctor_get(x_1897, 1);
lean_inc(x_1898);
lean_dec(x_1897);
x_1899 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1899, 0, x_1894);
lean_ctor_set(x_1899, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1900 = l_Lean_Compiler_LCNF_Simp_simp(x_1899, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1898);
if (lean_obj_tag(x_1900) == 0)
{
lean_object* x_1901; lean_object* x_1902; 
x_1901 = lean_ctor_get(x_1900, 0);
lean_inc(x_1901);
x_1902 = lean_ctor_get(x_1900, 1);
lean_inc(x_1902);
lean_dec(x_1900);
x_1850 = x_1901;
x_1851 = x_1902;
goto block_1874;
}
else
{
lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; 
lean_dec(x_1847);
lean_dec(x_1845);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1903 = lean_ctor_get(x_1900, 0);
lean_inc(x_1903);
x_1904 = lean_ctor_get(x_1900, 1);
lean_inc(x_1904);
if (lean_is_exclusive(x_1900)) {
 lean_ctor_release(x_1900, 0);
 lean_ctor_release(x_1900, 1);
 x_1905 = x_1900;
} else {
 lean_dec_ref(x_1900);
 x_1905 = lean_box(0);
}
if (lean_is_scalar(x_1905)) {
 x_1906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1906 = x_1905;
}
lean_ctor_set(x_1906, 0, x_1903);
lean_ctor_set(x_1906, 1, x_1904);
return x_1906;
}
}
else
{
lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; 
lean_dec(x_1894);
lean_dec(x_1847);
lean_dec(x_1845);
lean_dec(x_1537);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1907 = lean_ctor_get(x_1897, 0);
lean_inc(x_1907);
x_1908 = lean_ctor_get(x_1897, 1);
lean_inc(x_1908);
if (lean_is_exclusive(x_1897)) {
 lean_ctor_release(x_1897, 0);
 lean_ctor_release(x_1897, 1);
 x_1909 = x_1897;
} else {
 lean_dec_ref(x_1897);
 x_1909 = lean_box(0);
}
if (lean_is_scalar(x_1909)) {
 x_1910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1910 = x_1909;
}
lean_ctor_set(x_1910, 0, x_1907);
lean_ctor_set(x_1910, 1, x_1908);
return x_1910;
}
}
else
{
lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
lean_dec(x_1847);
lean_dec(x_1845);
lean_dec(x_1537);
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
x_1911 = lean_ctor_get(x_1893, 0);
lean_inc(x_1911);
x_1912 = lean_ctor_get(x_1893, 1);
lean_inc(x_1912);
if (lean_is_exclusive(x_1893)) {
 lean_ctor_release(x_1893, 0);
 lean_ctor_release(x_1893, 1);
 x_1913 = x_1893;
} else {
 lean_dec_ref(x_1893);
 x_1913 = lean_box(0);
}
if (lean_is_scalar(x_1913)) {
 x_1914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1914 = x_1913;
}
lean_ctor_set(x_1914, 0, x_1911);
lean_ctor_set(x_1914, 1, x_1912);
return x_1914;
}
}
block_1874:
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; 
x_1852 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1853 = lean_array_push(x_1852, x_1845);
x_1854 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_1855 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1853, x_1850, x_1854, x_6, x_7, x_8, x_9, x_1851);
if (lean_obj_tag(x_1855) == 0)
{
lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; 
x_1856 = lean_ctor_get(x_1855, 0);
lean_inc(x_1856);
x_1857 = lean_ctor_get(x_1855, 1);
lean_inc(x_1857);
lean_dec(x_1855);
lean_inc(x_1856);
x_1858 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1858, 0, x_1856);
lean_closure_set(x_1858, 1, x_1852);
x_1859 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1537, x_1858, x_6, x_7, x_8, x_9, x_1857);
if (lean_obj_tag(x_1859) == 0)
{
lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; 
x_1860 = lean_ctor_get(x_1859, 0);
lean_inc(x_1860);
x_1861 = lean_ctor_get(x_1859, 1);
lean_inc(x_1861);
if (lean_is_exclusive(x_1859)) {
 lean_ctor_release(x_1859, 0);
 lean_ctor_release(x_1859, 1);
 x_1862 = x_1859;
} else {
 lean_dec_ref(x_1859);
 x_1862 = lean_box(0);
}
if (lean_is_scalar(x_1847)) {
 x_1863 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1863 = x_1847;
 lean_ctor_set_tag(x_1863, 2);
}
lean_ctor_set(x_1863, 0, x_1856);
lean_ctor_set(x_1863, 1, x_1860);
if (lean_is_scalar(x_22)) {
 x_1864 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1864 = x_22;
}
lean_ctor_set(x_1864, 0, x_1863);
if (lean_is_scalar(x_1862)) {
 x_1865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1865 = x_1862;
}
lean_ctor_set(x_1865, 0, x_1864);
lean_ctor_set(x_1865, 1, x_1861);
return x_1865;
}
else
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; 
lean_dec(x_1856);
lean_dec(x_1847);
lean_dec(x_22);
x_1866 = lean_ctor_get(x_1859, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1859, 1);
lean_inc(x_1867);
if (lean_is_exclusive(x_1859)) {
 lean_ctor_release(x_1859, 0);
 lean_ctor_release(x_1859, 1);
 x_1868 = x_1859;
} else {
 lean_dec_ref(x_1859);
 x_1868 = lean_box(0);
}
if (lean_is_scalar(x_1868)) {
 x_1869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1869 = x_1868;
}
lean_ctor_set(x_1869, 0, x_1866);
lean_ctor_set(x_1869, 1, x_1867);
return x_1869;
}
}
else
{
lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; 
lean_dec(x_1847);
lean_dec(x_1537);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1870 = lean_ctor_get(x_1855, 0);
lean_inc(x_1870);
x_1871 = lean_ctor_get(x_1855, 1);
lean_inc(x_1871);
if (lean_is_exclusive(x_1855)) {
 lean_ctor_release(x_1855, 0);
 lean_ctor_release(x_1855, 1);
 x_1872 = x_1855;
} else {
 lean_dec_ref(x_1855);
 x_1872 = lean_box(0);
}
if (lean_is_scalar(x_1872)) {
 x_1873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1873 = x_1872;
}
lean_ctor_set(x_1873, 0, x_1870);
lean_ctor_set(x_1873, 1, x_1871);
return x_1873;
}
}
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; 
lean_dec(x_1839);
x_1915 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_1916 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1917 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1915, x_1537, x_1916, x_6, x_7, x_8, x_9, x_1840);
if (lean_obj_tag(x_1917) == 0)
{
lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; 
x_1918 = lean_ctor_get(x_1917, 0);
lean_inc(x_1918);
x_1919 = lean_ctor_get(x_1917, 1);
lean_inc(x_1919);
lean_dec(x_1917);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1920 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1918, x_6, x_7, x_8, x_9, x_1919);
if (lean_obj_tag(x_1920) == 0)
{
lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; uint8_t x_1924; lean_object* x_1925; lean_object* x_1926; 
x_1921 = lean_ctor_get(x_1920, 0);
lean_inc(x_1921);
x_1922 = lean_ctor_get(x_1920, 1);
lean_inc(x_1922);
lean_dec(x_1920);
x_1923 = lean_ctor_get(x_1921, 0);
lean_inc(x_1923);
x_1924 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1924 == 0)
{
lean_object* x_1937; 
lean_dec(x_1841);
lean_dec(x_27);
lean_dec(x_23);
x_1937 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1923, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1922);
if (lean_obj_tag(x_1937) == 0)
{
lean_object* x_1938; lean_object* x_1939; 
x_1938 = lean_ctor_get(x_1937, 1);
lean_inc(x_1938);
lean_dec(x_1937);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1939 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1938);
if (lean_obj_tag(x_1939) == 0)
{
lean_object* x_1940; lean_object* x_1941; 
x_1940 = lean_ctor_get(x_1939, 0);
lean_inc(x_1940);
x_1941 = lean_ctor_get(x_1939, 1);
lean_inc(x_1941);
lean_dec(x_1939);
x_1925 = x_1940;
x_1926 = x_1941;
goto block_1936;
}
else
{
lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; 
lean_dec(x_1921);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1942 = lean_ctor_get(x_1939, 0);
lean_inc(x_1942);
x_1943 = lean_ctor_get(x_1939, 1);
lean_inc(x_1943);
if (lean_is_exclusive(x_1939)) {
 lean_ctor_release(x_1939, 0);
 lean_ctor_release(x_1939, 1);
 x_1944 = x_1939;
} else {
 lean_dec_ref(x_1939);
 x_1944 = lean_box(0);
}
if (lean_is_scalar(x_1944)) {
 x_1945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1945 = x_1944;
}
lean_ctor_set(x_1945, 0, x_1942);
lean_ctor_set(x_1945, 1, x_1943);
return x_1945;
}
}
else
{
lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; 
lean_dec(x_1921);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1946 = lean_ctor_get(x_1937, 0);
lean_inc(x_1946);
x_1947 = lean_ctor_get(x_1937, 1);
lean_inc(x_1947);
if (lean_is_exclusive(x_1937)) {
 lean_ctor_release(x_1937, 0);
 lean_ctor_release(x_1937, 1);
 x_1948 = x_1937;
} else {
 lean_dec_ref(x_1937);
 x_1948 = lean_box(0);
}
if (lean_is_scalar(x_1948)) {
 x_1949 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1949 = x_1948;
}
lean_ctor_set(x_1949, 0, x_1946);
lean_ctor_set(x_1949, 1, x_1947);
return x_1949;
}
}
else
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; 
x_1950 = lean_array_get_size(x_23);
x_1951 = l_Array_toSubarray___rarg(x_23, x_27, x_1950);
x_1952 = l_Array_ofSubarray___rarg(x_1951);
lean_dec(x_1951);
if (lean_is_scalar(x_1841)) {
 x_1953 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1953 = x_1841;
 lean_ctor_set_tag(x_1953, 4);
}
lean_ctor_set(x_1953, 0, x_1923);
lean_ctor_set(x_1953, 1, x_1952);
x_1954 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1955 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1953, x_1954, x_6, x_7, x_8, x_9, x_1922);
if (lean_obj_tag(x_1955) == 0)
{
lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; 
x_1956 = lean_ctor_get(x_1955, 0);
lean_inc(x_1956);
x_1957 = lean_ctor_get(x_1955, 1);
lean_inc(x_1957);
lean_dec(x_1955);
x_1958 = lean_ctor_get(x_1956, 0);
lean_inc(x_1958);
x_1959 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1958, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1957);
if (lean_obj_tag(x_1959) == 0)
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; 
x_1960 = lean_ctor_get(x_1959, 1);
lean_inc(x_1960);
lean_dec(x_1959);
x_1961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1961, 0, x_1956);
lean_ctor_set(x_1961, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1962 = l_Lean_Compiler_LCNF_Simp_simp(x_1961, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1960);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; lean_object* x_1964; 
x_1963 = lean_ctor_get(x_1962, 0);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1962, 1);
lean_inc(x_1964);
lean_dec(x_1962);
x_1925 = x_1963;
x_1926 = x_1964;
goto block_1936;
}
else
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; 
lean_dec(x_1921);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1965 = lean_ctor_get(x_1962, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1962, 1);
lean_inc(x_1966);
if (lean_is_exclusive(x_1962)) {
 lean_ctor_release(x_1962, 0);
 lean_ctor_release(x_1962, 1);
 x_1967 = x_1962;
} else {
 lean_dec_ref(x_1962);
 x_1967 = lean_box(0);
}
if (lean_is_scalar(x_1967)) {
 x_1968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1968 = x_1967;
}
lean_ctor_set(x_1968, 0, x_1965);
lean_ctor_set(x_1968, 1, x_1966);
return x_1968;
}
}
else
{
lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; 
lean_dec(x_1956);
lean_dec(x_1921);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1969 = lean_ctor_get(x_1959, 0);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1959, 1);
lean_inc(x_1970);
if (lean_is_exclusive(x_1959)) {
 lean_ctor_release(x_1959, 0);
 lean_ctor_release(x_1959, 1);
 x_1971 = x_1959;
} else {
 lean_dec_ref(x_1959);
 x_1971 = lean_box(0);
}
if (lean_is_scalar(x_1971)) {
 x_1972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1972 = x_1971;
}
lean_ctor_set(x_1972, 0, x_1969);
lean_ctor_set(x_1972, 1, x_1970);
return x_1972;
}
}
else
{
lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; 
lean_dec(x_1921);
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
x_1973 = lean_ctor_get(x_1955, 0);
lean_inc(x_1973);
x_1974 = lean_ctor_get(x_1955, 1);
lean_inc(x_1974);
if (lean_is_exclusive(x_1955)) {
 lean_ctor_release(x_1955, 0);
 lean_ctor_release(x_1955, 1);
 x_1975 = x_1955;
} else {
 lean_dec_ref(x_1955);
 x_1975 = lean_box(0);
}
if (lean_is_scalar(x_1975)) {
 x_1976 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1976 = x_1975;
}
lean_ctor_set(x_1976, 0, x_1973);
lean_ctor_set(x_1976, 1, x_1974);
return x_1976;
}
}
block_1936:
{
lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; 
x_1927 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1927, 0, x_1921);
x_1928 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_1929 = lean_array_push(x_1928, x_1927);
x_1930 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1929, x_1925, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1926);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1929);
x_1931 = lean_ctor_get(x_1930, 0);
lean_inc(x_1931);
x_1932 = lean_ctor_get(x_1930, 1);
lean_inc(x_1932);
if (lean_is_exclusive(x_1930)) {
 lean_ctor_release(x_1930, 0);
 lean_ctor_release(x_1930, 1);
 x_1933 = x_1930;
} else {
 lean_dec_ref(x_1930);
 x_1933 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1934 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1934 = x_22;
}
lean_ctor_set(x_1934, 0, x_1931);
if (lean_is_scalar(x_1933)) {
 x_1935 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1935 = x_1933;
}
lean_ctor_set(x_1935, 0, x_1934);
lean_ctor_set(x_1935, 1, x_1932);
return x_1935;
}
}
else
{
lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; 
lean_dec(x_1841);
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
x_1977 = lean_ctor_get(x_1920, 0);
lean_inc(x_1977);
x_1978 = lean_ctor_get(x_1920, 1);
lean_inc(x_1978);
if (lean_is_exclusive(x_1920)) {
 lean_ctor_release(x_1920, 0);
 lean_ctor_release(x_1920, 1);
 x_1979 = x_1920;
} else {
 lean_dec_ref(x_1920);
 x_1979 = lean_box(0);
}
if (lean_is_scalar(x_1979)) {
 x_1980 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1980 = x_1979;
}
lean_ctor_set(x_1980, 0, x_1977);
lean_ctor_set(x_1980, 1, x_1978);
return x_1980;
}
}
else
{
lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; 
lean_dec(x_1841);
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
x_1981 = lean_ctor_get(x_1917, 0);
lean_inc(x_1981);
x_1982 = lean_ctor_get(x_1917, 1);
lean_inc(x_1982);
if (lean_is_exclusive(x_1917)) {
 lean_ctor_release(x_1917, 0);
 lean_ctor_release(x_1917, 1);
 x_1983 = x_1917;
} else {
 lean_dec_ref(x_1917);
 x_1983 = lean_box(0);
}
if (lean_is_scalar(x_1983)) {
 x_1984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1984 = x_1983;
}
lean_ctor_set(x_1984, 0, x_1981);
lean_ctor_set(x_1984, 1, x_1982);
return x_1984;
}
}
}
}
else
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
lean_dec(x_33);
lean_dec(x_21);
x_1985 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1538);
x_1986 = lean_ctor_get(x_1985, 1);
lean_inc(x_1986);
lean_dec(x_1985);
x_1987 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_1987, 0, x_3);
lean_closure_set(x_1987, 1, x_4);
lean_closure_set(x_1987, 2, x_5);
lean_closure_set(x_1987, 3, x_27);
lean_closure_set(x_1987, 4, x_24);
lean_closure_set(x_1987, 5, x_26);
lean_closure_set(x_1987, 6, x_2);
lean_closure_set(x_1987, 7, x_23);
x_1988 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1537, x_1987, x_6, x_7, x_8, x_9, x_1986);
if (lean_obj_tag(x_1988) == 0)
{
uint8_t x_1989; 
x_1989 = !lean_is_exclusive(x_1988);
if (x_1989 == 0)
{
lean_object* x_1990; lean_object* x_1991; 
x_1990 = lean_ctor_get(x_1988, 0);
if (lean_is_scalar(x_22)) {
 x_1991 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1991 = x_22;
}
lean_ctor_set(x_1991, 0, x_1990);
lean_ctor_set(x_1988, 0, x_1991);
return x_1988;
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
x_1992 = lean_ctor_get(x_1988, 0);
x_1993 = lean_ctor_get(x_1988, 1);
lean_inc(x_1993);
lean_inc(x_1992);
lean_dec(x_1988);
if (lean_is_scalar(x_22)) {
 x_1994 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1994 = x_22;
}
lean_ctor_set(x_1994, 0, x_1992);
x_1995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1995, 0, x_1994);
lean_ctor_set(x_1995, 1, x_1993);
return x_1995;
}
}
else
{
uint8_t x_1996; 
lean_dec(x_22);
x_1996 = !lean_is_exclusive(x_1988);
if (x_1996 == 0)
{
return x_1988;
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; 
x_1997 = lean_ctor_get(x_1988, 0);
x_1998 = lean_ctor_get(x_1988, 1);
lean_inc(x_1998);
lean_inc(x_1997);
lean_dec(x_1988);
x_1999 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1999, 0, x_1997);
lean_ctor_set(x_1999, 1, x_1998);
return x_1999;
}
}
}
}
else
{
uint8_t x_2000; 
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
x_2000 = !lean_is_exclusive(x_1536);
if (x_2000 == 0)
{
return x_1536;
}
else
{
lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; 
x_2001 = lean_ctor_get(x_1536, 0);
x_2002 = lean_ctor_get(x_1536, 1);
lean_inc(x_2002);
lean_inc(x_2001);
lean_dec(x_1536);
x_2003 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2003, 0, x_2001);
lean_ctor_set(x_2003, 1, x_2002);
return x_2003;
}
}
}
}
else
{
uint8_t x_2023; 
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
x_2023 = !lean_is_exclusive(x_1532);
if (x_2023 == 0)
{
return x_1532;
}
else
{
lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
x_2024 = lean_ctor_get(x_1532, 0);
x_2025 = lean_ctor_get(x_1532, 1);
lean_inc(x_2025);
lean_inc(x_2024);
lean_dec(x_1532);
x_2026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2026, 0, x_2024);
lean_ctor_set(x_2026, 1, x_2025);
return x_2026;
}
}
}
else
{
lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; uint8_t x_2034; lean_object* x_2035; 
x_2027 = lean_ctor_get(x_3, 0);
x_2028 = lean_ctor_get(x_3, 1);
x_2029 = lean_ctor_get(x_3, 2);
x_2030 = lean_ctor_get(x_3, 3);
lean_inc(x_2030);
lean_inc(x_2029);
lean_inc(x_2028);
lean_inc(x_2027);
lean_dec(x_3);
lean_inc(x_1522);
x_2031 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2031, 0, x_1522);
lean_ctor_set(x_2031, 1, x_2029);
x_2032 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_2030, x_1522, x_1524);
x_2033 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2033, 0, x_2027);
lean_ctor_set(x_2033, 1, x_2028);
lean_ctor_set(x_2033, 2, x_2031);
lean_ctor_set(x_2033, 3, x_2032);
x_2034 = 0;
lean_inc(x_33);
x_2035 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_2034, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_1525);
lean_dec(x_29);
if (lean_obj_tag(x_2035) == 0)
{
lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; uint8_t x_2212; 
x_2036 = lean_ctor_get(x_2035, 0);
lean_inc(x_2036);
x_2037 = lean_ctor_get(x_2035, 1);
lean_inc(x_2037);
lean_dec(x_2035);
x_2212 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2212 == 0)
{
lean_object* x_2213; 
x_2213 = lean_box(0);
x_2038 = x_2213;
goto block_2211;
}
else
{
uint8_t x_2214; 
x_2214 = lean_nat_dec_eq(x_24, x_27);
if (x_2214 == 0)
{
lean_object* x_2215; 
x_2215 = lean_box(0);
x_2038 = x_2215;
goto block_2211;
}
else
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_2216 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2037);
x_2217 = lean_ctor_get(x_2216, 1);
lean_inc(x_2217);
lean_dec(x_2216);
x_2218 = l_Lean_Compiler_LCNF_Simp_simp(x_2036, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2217);
if (lean_obj_tag(x_2218) == 0)
{
lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; 
x_2219 = lean_ctor_get(x_2218, 0);
lean_inc(x_2219);
x_2220 = lean_ctor_get(x_2218, 1);
lean_inc(x_2220);
if (lean_is_exclusive(x_2218)) {
 lean_ctor_release(x_2218, 0);
 lean_ctor_release(x_2218, 1);
 x_2221 = x_2218;
} else {
 lean_dec_ref(x_2218);
 x_2221 = lean_box(0);
}
x_2222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2222, 0, x_2219);
if (lean_is_scalar(x_2221)) {
 x_2223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2223 = x_2221;
}
lean_ctor_set(x_2223, 0, x_2222);
lean_ctor_set(x_2223, 1, x_2220);
return x_2223;
}
else
{
lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; 
x_2224 = lean_ctor_get(x_2218, 0);
lean_inc(x_2224);
x_2225 = lean_ctor_get(x_2218, 1);
lean_inc(x_2225);
if (lean_is_exclusive(x_2218)) {
 lean_ctor_release(x_2218, 0);
 lean_ctor_release(x_2218, 1);
 x_2226 = x_2218;
} else {
 lean_dec_ref(x_2218);
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
}
block_2211:
{
lean_object* x_2039; 
lean_dec(x_2038);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2033);
x_2039 = l_Lean_Compiler_LCNF_Simp_simp(x_2036, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2037);
if (lean_obj_tag(x_2039) == 0)
{
lean_object* x_2040; lean_object* x_2041; uint8_t x_2042; 
x_2040 = lean_ctor_get(x_2039, 0);
lean_inc(x_2040);
x_2041 = lean_ctor_get(x_2039, 1);
lean_inc(x_2041);
lean_dec(x_2039);
lean_inc(x_2040);
x_2042 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_2040);
if (x_2042 == 0)
{
lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; uint8_t x_2052; 
x_2043 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2041);
x_2044 = lean_ctor_get(x_2043, 1);
lean_inc(x_2044);
if (lean_is_exclusive(x_2043)) {
 lean_ctor_release(x_2043, 0);
 lean_ctor_release(x_2043, 1);
 x_2045 = x_2043;
} else {
 lean_dec_ref(x_2043);
 x_2045 = lean_box(0);
}
x_2046 = lean_ctor_get(x_21, 2);
lean_inc(x_2046);
lean_dec(x_21);
x_2047 = l_Lean_Compiler_LCNF_inferAppType(x_2046, x_33, x_6, x_7, x_8, x_9, x_2044);
x_2048 = lean_ctor_get(x_2047, 0);
lean_inc(x_2048);
x_2049 = lean_ctor_get(x_2047, 1);
lean_inc(x_2049);
if (lean_is_exclusive(x_2047)) {
 lean_ctor_release(x_2047, 0);
 lean_ctor_release(x_2047, 1);
 x_2050 = x_2047;
} else {
 lean_dec_ref(x_2047);
 x_2050 = lean_box(0);
}
lean_inc(x_2048);
x_2051 = l_Lean_Expr_headBeta(x_2048);
x_2052 = l_Lean_Expr_isForall(x_2051);
lean_dec(x_2051);
if (x_2052 == 0)
{
lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; uint8_t x_2058; lean_object* x_2059; lean_object* x_2060; 
x_2053 = l_Lean_Compiler_LCNF_mkAuxParam(x_2048, x_2034, x_6, x_7, x_8, x_9, x_2049);
x_2054 = lean_ctor_get(x_2053, 0);
lean_inc(x_2054);
x_2055 = lean_ctor_get(x_2053, 1);
lean_inc(x_2055);
if (lean_is_exclusive(x_2053)) {
 lean_ctor_release(x_2053, 0);
 lean_ctor_release(x_2053, 1);
 x_2056 = x_2053;
} else {
 lean_dec_ref(x_2053);
 x_2056 = lean_box(0);
}
x_2057 = lean_ctor_get(x_2054, 0);
lean_inc(x_2057);
x_2058 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2058 == 0)
{
lean_object* x_2084; 
lean_dec(x_2050);
lean_dec(x_2045);
lean_dec(x_27);
lean_dec(x_23);
x_2084 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2057, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2055);
if (lean_obj_tag(x_2084) == 0)
{
lean_object* x_2085; lean_object* x_2086; 
x_2085 = lean_ctor_get(x_2084, 1);
lean_inc(x_2085);
lean_dec(x_2084);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2086 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2085);
if (lean_obj_tag(x_2086) == 0)
{
lean_object* x_2087; lean_object* x_2088; 
x_2087 = lean_ctor_get(x_2086, 0);
lean_inc(x_2087);
x_2088 = lean_ctor_get(x_2086, 1);
lean_inc(x_2088);
lean_dec(x_2086);
x_2059 = x_2087;
x_2060 = x_2088;
goto block_2083;
}
else
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2040);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2089 = lean_ctor_get(x_2086, 0);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2086, 1);
lean_inc(x_2090);
if (lean_is_exclusive(x_2086)) {
 lean_ctor_release(x_2086, 0);
 lean_ctor_release(x_2086, 1);
 x_2091 = x_2086;
} else {
 lean_dec_ref(x_2086);
 x_2091 = lean_box(0);
}
if (lean_is_scalar(x_2091)) {
 x_2092 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2092 = x_2091;
}
lean_ctor_set(x_2092, 0, x_2089);
lean_ctor_set(x_2092, 1, x_2090);
return x_2092;
}
}
else
{
lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2040);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2093 = lean_ctor_get(x_2084, 0);
lean_inc(x_2093);
x_2094 = lean_ctor_get(x_2084, 1);
lean_inc(x_2094);
if (lean_is_exclusive(x_2084)) {
 lean_ctor_release(x_2084, 0);
 lean_ctor_release(x_2084, 1);
 x_2095 = x_2084;
} else {
 lean_dec_ref(x_2084);
 x_2095 = lean_box(0);
}
if (lean_is_scalar(x_2095)) {
 x_2096 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2096 = x_2095;
}
lean_ctor_set(x_2096, 0, x_2093);
lean_ctor_set(x_2096, 1, x_2094);
return x_2096;
}
}
else
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; 
x_2097 = lean_array_get_size(x_23);
x_2098 = l_Array_toSubarray___rarg(x_23, x_27, x_2097);
x_2099 = l_Array_ofSubarray___rarg(x_2098);
lean_dec(x_2098);
if (lean_is_scalar(x_2050)) {
 x_2100 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2100 = x_2050;
 lean_ctor_set_tag(x_2100, 4);
}
lean_ctor_set(x_2100, 0, x_2057);
lean_ctor_set(x_2100, 1, x_2099);
x_2101 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2102 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2100, x_2101, x_6, x_7, x_8, x_9, x_2055);
if (lean_obj_tag(x_2102) == 0)
{
lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; 
x_2103 = lean_ctor_get(x_2102, 0);
lean_inc(x_2103);
x_2104 = lean_ctor_get(x_2102, 1);
lean_inc(x_2104);
lean_dec(x_2102);
x_2105 = lean_ctor_get(x_2103, 0);
lean_inc(x_2105);
x_2106 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2105, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2104);
if (lean_obj_tag(x_2106) == 0)
{
lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; 
x_2107 = lean_ctor_get(x_2106, 1);
lean_inc(x_2107);
lean_dec(x_2106);
if (lean_is_scalar(x_2045)) {
 x_2108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2108 = x_2045;
}
lean_ctor_set(x_2108, 0, x_2103);
lean_ctor_set(x_2108, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2109 = l_Lean_Compiler_LCNF_Simp_simp(x_2108, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2107);
if (lean_obj_tag(x_2109) == 0)
{
lean_object* x_2110; lean_object* x_2111; 
x_2110 = lean_ctor_get(x_2109, 0);
lean_inc(x_2110);
x_2111 = lean_ctor_get(x_2109, 1);
lean_inc(x_2111);
lean_dec(x_2109);
x_2059 = x_2110;
x_2060 = x_2111;
goto block_2083;
}
else
{
lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2040);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2112 = lean_ctor_get(x_2109, 0);
lean_inc(x_2112);
x_2113 = lean_ctor_get(x_2109, 1);
lean_inc(x_2113);
if (lean_is_exclusive(x_2109)) {
 lean_ctor_release(x_2109, 0);
 lean_ctor_release(x_2109, 1);
 x_2114 = x_2109;
} else {
 lean_dec_ref(x_2109);
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
lean_dec(x_2103);
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2045);
lean_dec(x_2040);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2116 = lean_ctor_get(x_2106, 0);
lean_inc(x_2116);
x_2117 = lean_ctor_get(x_2106, 1);
lean_inc(x_2117);
if (lean_is_exclusive(x_2106)) {
 lean_ctor_release(x_2106, 0);
 lean_ctor_release(x_2106, 1);
 x_2118 = x_2106;
} else {
 lean_dec_ref(x_2106);
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
else
{
lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; 
lean_dec(x_2056);
lean_dec(x_2054);
lean_dec(x_2045);
lean_dec(x_2040);
lean_dec(x_2033);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2120 = lean_ctor_get(x_2102, 0);
lean_inc(x_2120);
x_2121 = lean_ctor_get(x_2102, 1);
lean_inc(x_2121);
if (lean_is_exclusive(x_2102)) {
 lean_ctor_release(x_2102, 0);
 lean_ctor_release(x_2102, 1);
 x_2122 = x_2102;
} else {
 lean_dec_ref(x_2102);
 x_2122 = lean_box(0);
}
if (lean_is_scalar(x_2122)) {
 x_2123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2123 = x_2122;
}
lean_ctor_set(x_2123, 0, x_2120);
lean_ctor_set(x_2123, 1, x_2121);
return x_2123;
}
}
block_2083:
{
lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; 
x_2061 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2062 = lean_array_push(x_2061, x_2054);
x_2063 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_2064 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2062, x_2059, x_2063, x_6, x_7, x_8, x_9, x_2060);
if (lean_obj_tag(x_2064) == 0)
{
lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; 
x_2065 = lean_ctor_get(x_2064, 0);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_2064, 1);
lean_inc(x_2066);
lean_dec(x_2064);
lean_inc(x_2065);
x_2067 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_2067, 0, x_2065);
lean_closure_set(x_2067, 1, x_2061);
x_2068 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2040, x_2067, x_6, x_7, x_8, x_9, x_2066);
if (lean_obj_tag(x_2068) == 0)
{
lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
x_2069 = lean_ctor_get(x_2068, 0);
lean_inc(x_2069);
x_2070 = lean_ctor_get(x_2068, 1);
lean_inc(x_2070);
if (lean_is_exclusive(x_2068)) {
 lean_ctor_release(x_2068, 0);
 lean_ctor_release(x_2068, 1);
 x_2071 = x_2068;
} else {
 lean_dec_ref(x_2068);
 x_2071 = lean_box(0);
}
if (lean_is_scalar(x_2056)) {
 x_2072 = lean_alloc_ctor(2, 2, 0);
} else {
 x_2072 = x_2056;
 lean_ctor_set_tag(x_2072, 2);
}
lean_ctor_set(x_2072, 0, x_2065);
lean_ctor_set(x_2072, 1, x_2069);
if (lean_is_scalar(x_22)) {
 x_2073 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2073 = x_22;
}
lean_ctor_set(x_2073, 0, x_2072);
if (lean_is_scalar(x_2071)) {
 x_2074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2074 = x_2071;
}
lean_ctor_set(x_2074, 0, x_2073);
lean_ctor_set(x_2074, 1, x_2070);
return x_2074;
}
else
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
lean_dec(x_2065);
lean_dec(x_2056);
lean_dec(x_22);
x_2075 = lean_ctor_get(x_2068, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2068, 1);
lean_inc(x_2076);
if (lean_is_exclusive(x_2068)) {
 lean_ctor_release(x_2068, 0);
 lean_ctor_release(x_2068, 1);
 x_2077 = x_2068;
} else {
 lean_dec_ref(x_2068);
 x_2077 = lean_box(0);
}
if (lean_is_scalar(x_2077)) {
 x_2078 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2078 = x_2077;
}
lean_ctor_set(x_2078, 0, x_2075);
lean_ctor_set(x_2078, 1, x_2076);
return x_2078;
}
}
else
{
lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; 
lean_dec(x_2056);
lean_dec(x_2040);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2079 = lean_ctor_get(x_2064, 0);
lean_inc(x_2079);
x_2080 = lean_ctor_get(x_2064, 1);
lean_inc(x_2080);
if (lean_is_exclusive(x_2064)) {
 lean_ctor_release(x_2064, 0);
 lean_ctor_release(x_2064, 1);
 x_2081 = x_2064;
} else {
 lean_dec_ref(x_2064);
 x_2081 = lean_box(0);
}
if (lean_is_scalar(x_2081)) {
 x_2082 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2082 = x_2081;
}
lean_ctor_set(x_2082, 0, x_2079);
lean_ctor_set(x_2082, 1, x_2080);
return x_2082;
}
}
}
else
{
lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
lean_dec(x_2048);
x_2124 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2125 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_2126 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2124, x_2040, x_2125, x_6, x_7, x_8, x_9, x_2049);
if (lean_obj_tag(x_2126) == 0)
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2127 = lean_ctor_get(x_2126, 0);
lean_inc(x_2127);
x_2128 = lean_ctor_get(x_2126, 1);
lean_inc(x_2128);
lean_dec(x_2126);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2129 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2127, x_6, x_7, x_8, x_9, x_2128);
if (lean_obj_tag(x_2129) == 0)
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; uint8_t x_2133; lean_object* x_2134; lean_object* x_2135; 
x_2130 = lean_ctor_get(x_2129, 0);
lean_inc(x_2130);
x_2131 = lean_ctor_get(x_2129, 1);
lean_inc(x_2131);
lean_dec(x_2129);
x_2132 = lean_ctor_get(x_2130, 0);
lean_inc(x_2132);
x_2133 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2133 == 0)
{
lean_object* x_2146; 
lean_dec(x_2050);
lean_dec(x_2045);
lean_dec(x_27);
lean_dec(x_23);
x_2146 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2132, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2131);
if (lean_obj_tag(x_2146) == 0)
{
lean_object* x_2147; lean_object* x_2148; 
x_2147 = lean_ctor_get(x_2146, 1);
lean_inc(x_2147);
lean_dec(x_2146);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2033);
x_2148 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2147);
if (lean_obj_tag(x_2148) == 0)
{
lean_object* x_2149; lean_object* x_2150; 
x_2149 = lean_ctor_get(x_2148, 0);
lean_inc(x_2149);
x_2150 = lean_ctor_get(x_2148, 1);
lean_inc(x_2150);
lean_dec(x_2148);
x_2134 = x_2149;
x_2135 = x_2150;
goto block_2145;
}
else
{
lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; 
lean_dec(x_2130);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2151 = lean_ctor_get(x_2148, 0);
lean_inc(x_2151);
x_2152 = lean_ctor_get(x_2148, 1);
lean_inc(x_2152);
if (lean_is_exclusive(x_2148)) {
 lean_ctor_release(x_2148, 0);
 lean_ctor_release(x_2148, 1);
 x_2153 = x_2148;
} else {
 lean_dec_ref(x_2148);
 x_2153 = lean_box(0);
}
if (lean_is_scalar(x_2153)) {
 x_2154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2154 = x_2153;
}
lean_ctor_set(x_2154, 0, x_2151);
lean_ctor_set(x_2154, 1, x_2152);
return x_2154;
}
}
else
{
lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; 
lean_dec(x_2130);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2155 = lean_ctor_get(x_2146, 0);
lean_inc(x_2155);
x_2156 = lean_ctor_get(x_2146, 1);
lean_inc(x_2156);
if (lean_is_exclusive(x_2146)) {
 lean_ctor_release(x_2146, 0);
 lean_ctor_release(x_2146, 1);
 x_2157 = x_2146;
} else {
 lean_dec_ref(x_2146);
 x_2157 = lean_box(0);
}
if (lean_is_scalar(x_2157)) {
 x_2158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2158 = x_2157;
}
lean_ctor_set(x_2158, 0, x_2155);
lean_ctor_set(x_2158, 1, x_2156);
return x_2158;
}
}
else
{
lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; 
x_2159 = lean_array_get_size(x_23);
x_2160 = l_Array_toSubarray___rarg(x_23, x_27, x_2159);
x_2161 = l_Array_ofSubarray___rarg(x_2160);
lean_dec(x_2160);
if (lean_is_scalar(x_2050)) {
 x_2162 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2162 = x_2050;
 lean_ctor_set_tag(x_2162, 4);
}
lean_ctor_set(x_2162, 0, x_2132);
lean_ctor_set(x_2162, 1, x_2161);
x_2163 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2164 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2162, x_2163, x_6, x_7, x_8, x_9, x_2131);
if (lean_obj_tag(x_2164) == 0)
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; 
x_2165 = lean_ctor_get(x_2164, 0);
lean_inc(x_2165);
x_2166 = lean_ctor_get(x_2164, 1);
lean_inc(x_2166);
lean_dec(x_2164);
x_2167 = lean_ctor_get(x_2165, 0);
lean_inc(x_2167);
x_2168 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2167, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2166);
if (lean_obj_tag(x_2168) == 0)
{
lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; 
x_2169 = lean_ctor_get(x_2168, 1);
lean_inc(x_2169);
lean_dec(x_2168);
if (lean_is_scalar(x_2045)) {
 x_2170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2170 = x_2045;
}
lean_ctor_set(x_2170, 0, x_2165);
lean_ctor_set(x_2170, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2033);
x_2171 = l_Lean_Compiler_LCNF_Simp_simp(x_2170, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2169);
if (lean_obj_tag(x_2171) == 0)
{
lean_object* x_2172; lean_object* x_2173; 
x_2172 = lean_ctor_get(x_2171, 0);
lean_inc(x_2172);
x_2173 = lean_ctor_get(x_2171, 1);
lean_inc(x_2173);
lean_dec(x_2171);
x_2134 = x_2172;
x_2135 = x_2173;
goto block_2145;
}
else
{
lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; 
lean_dec(x_2130);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2174 = lean_ctor_get(x_2171, 0);
lean_inc(x_2174);
x_2175 = lean_ctor_get(x_2171, 1);
lean_inc(x_2175);
if (lean_is_exclusive(x_2171)) {
 lean_ctor_release(x_2171, 0);
 lean_ctor_release(x_2171, 1);
 x_2176 = x_2171;
} else {
 lean_dec_ref(x_2171);
 x_2176 = lean_box(0);
}
if (lean_is_scalar(x_2176)) {
 x_2177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2177 = x_2176;
}
lean_ctor_set(x_2177, 0, x_2174);
lean_ctor_set(x_2177, 1, x_2175);
return x_2177;
}
}
else
{
lean_object* x_2178; lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; 
lean_dec(x_2165);
lean_dec(x_2130);
lean_dec(x_2045);
lean_dec(x_2033);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2178 = lean_ctor_get(x_2168, 0);
lean_inc(x_2178);
x_2179 = lean_ctor_get(x_2168, 1);
lean_inc(x_2179);
if (lean_is_exclusive(x_2168)) {
 lean_ctor_release(x_2168, 0);
 lean_ctor_release(x_2168, 1);
 x_2180 = x_2168;
} else {
 lean_dec_ref(x_2168);
 x_2180 = lean_box(0);
}
if (lean_is_scalar(x_2180)) {
 x_2181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2181 = x_2180;
}
lean_ctor_set(x_2181, 0, x_2178);
lean_ctor_set(x_2181, 1, x_2179);
return x_2181;
}
}
else
{
lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; 
lean_dec(x_2130);
lean_dec(x_2045);
lean_dec(x_2033);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2182 = lean_ctor_get(x_2164, 0);
lean_inc(x_2182);
x_2183 = lean_ctor_get(x_2164, 1);
lean_inc(x_2183);
if (lean_is_exclusive(x_2164)) {
 lean_ctor_release(x_2164, 0);
 lean_ctor_release(x_2164, 1);
 x_2184 = x_2164;
} else {
 lean_dec_ref(x_2164);
 x_2184 = lean_box(0);
}
if (lean_is_scalar(x_2184)) {
 x_2185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2185 = x_2184;
}
lean_ctor_set(x_2185, 0, x_2182);
lean_ctor_set(x_2185, 1, x_2183);
return x_2185;
}
}
block_2145:
{
lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2136, 0, x_2130);
x_2137 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2138 = lean_array_push(x_2137, x_2136);
x_2139 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2138, x_2134, x_2033, x_4, x_5, x_6, x_7, x_8, x_9, x_2135);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2033);
lean_dec(x_2138);
x_2140 = lean_ctor_get(x_2139, 0);
lean_inc(x_2140);
x_2141 = lean_ctor_get(x_2139, 1);
lean_inc(x_2141);
if (lean_is_exclusive(x_2139)) {
 lean_ctor_release(x_2139, 0);
 lean_ctor_release(x_2139, 1);
 x_2142 = x_2139;
} else {
 lean_dec_ref(x_2139);
 x_2142 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2143 = x_22;
}
lean_ctor_set(x_2143, 0, x_2140);
if (lean_is_scalar(x_2142)) {
 x_2144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2144 = x_2142;
}
lean_ctor_set(x_2144, 0, x_2143);
lean_ctor_set(x_2144, 1, x_2141);
return x_2144;
}
}
else
{
lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; 
lean_dec(x_2050);
lean_dec(x_2045);
lean_dec(x_2033);
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
x_2186 = lean_ctor_get(x_2129, 0);
lean_inc(x_2186);
x_2187 = lean_ctor_get(x_2129, 1);
lean_inc(x_2187);
if (lean_is_exclusive(x_2129)) {
 lean_ctor_release(x_2129, 0);
 lean_ctor_release(x_2129, 1);
 x_2188 = x_2129;
} else {
 lean_dec_ref(x_2129);
 x_2188 = lean_box(0);
}
if (lean_is_scalar(x_2188)) {
 x_2189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2189 = x_2188;
}
lean_ctor_set(x_2189, 0, x_2186);
lean_ctor_set(x_2189, 1, x_2187);
return x_2189;
}
}
else
{
lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; 
lean_dec(x_2050);
lean_dec(x_2045);
lean_dec(x_2033);
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
x_2190 = lean_ctor_get(x_2126, 0);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2126, 1);
lean_inc(x_2191);
if (lean_is_exclusive(x_2126)) {
 lean_ctor_release(x_2126, 0);
 lean_ctor_release(x_2126, 1);
 x_2192 = x_2126;
} else {
 lean_dec_ref(x_2126);
 x_2192 = lean_box(0);
}
if (lean_is_scalar(x_2192)) {
 x_2193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2193 = x_2192;
}
lean_ctor_set(x_2193, 0, x_2190);
lean_ctor_set(x_2193, 1, x_2191);
return x_2193;
}
}
}
else
{
lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; lean_object* x_2197; 
lean_dec(x_33);
lean_dec(x_21);
x_2194 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2041);
x_2195 = lean_ctor_get(x_2194, 1);
lean_inc(x_2195);
lean_dec(x_2194);
x_2196 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_2196, 0, x_2033);
lean_closure_set(x_2196, 1, x_4);
lean_closure_set(x_2196, 2, x_5);
lean_closure_set(x_2196, 3, x_27);
lean_closure_set(x_2196, 4, x_24);
lean_closure_set(x_2196, 5, x_26);
lean_closure_set(x_2196, 6, x_2);
lean_closure_set(x_2196, 7, x_23);
x_2197 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2040, x_2196, x_6, x_7, x_8, x_9, x_2195);
if (lean_obj_tag(x_2197) == 0)
{
lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; lean_object* x_2202; 
x_2198 = lean_ctor_get(x_2197, 0);
lean_inc(x_2198);
x_2199 = lean_ctor_get(x_2197, 1);
lean_inc(x_2199);
if (lean_is_exclusive(x_2197)) {
 lean_ctor_release(x_2197, 0);
 lean_ctor_release(x_2197, 1);
 x_2200 = x_2197;
} else {
 lean_dec_ref(x_2197);
 x_2200 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2201 = x_22;
}
lean_ctor_set(x_2201, 0, x_2198);
if (lean_is_scalar(x_2200)) {
 x_2202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2202 = x_2200;
}
lean_ctor_set(x_2202, 0, x_2201);
lean_ctor_set(x_2202, 1, x_2199);
return x_2202;
}
else
{
lean_object* x_2203; lean_object* x_2204; lean_object* x_2205; lean_object* x_2206; 
lean_dec(x_22);
x_2203 = lean_ctor_get(x_2197, 0);
lean_inc(x_2203);
x_2204 = lean_ctor_get(x_2197, 1);
lean_inc(x_2204);
if (lean_is_exclusive(x_2197)) {
 lean_ctor_release(x_2197, 0);
 lean_ctor_release(x_2197, 1);
 x_2205 = x_2197;
} else {
 lean_dec_ref(x_2197);
 x_2205 = lean_box(0);
}
if (lean_is_scalar(x_2205)) {
 x_2206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2206 = x_2205;
}
lean_ctor_set(x_2206, 0, x_2203);
lean_ctor_set(x_2206, 1, x_2204);
return x_2206;
}
}
}
else
{
lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; 
lean_dec(x_2033);
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
x_2207 = lean_ctor_get(x_2039, 0);
lean_inc(x_2207);
x_2208 = lean_ctor_get(x_2039, 1);
lean_inc(x_2208);
if (lean_is_exclusive(x_2039)) {
 lean_ctor_release(x_2039, 0);
 lean_ctor_release(x_2039, 1);
 x_2209 = x_2039;
} else {
 lean_dec_ref(x_2039);
 x_2209 = lean_box(0);
}
if (lean_is_scalar(x_2209)) {
 x_2210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2210 = x_2209;
}
lean_ctor_set(x_2210, 0, x_2207);
lean_ctor_set(x_2210, 1, x_2208);
return x_2210;
}
}
}
else
{
lean_object* x_2228; lean_object* x_2229; lean_object* x_2230; lean_object* x_2231; 
lean_dec(x_2033);
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
x_2228 = lean_ctor_get(x_2035, 0);
lean_inc(x_2228);
x_2229 = lean_ctor_get(x_2035, 1);
lean_inc(x_2229);
if (lean_is_exclusive(x_2035)) {
 lean_ctor_release(x_2035, 0);
 lean_ctor_release(x_2035, 1);
 x_2230 = x_2035;
} else {
 lean_dec_ref(x_2035);
 x_2230 = lean_box(0);
}
if (lean_is_scalar(x_2230)) {
 x_2231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2231 = x_2230;
}
lean_ctor_set(x_2231, 0, x_2228);
lean_ctor_set(x_2231, 1, x_2229);
return x_2231;
}
}
}
else
{
uint8_t x_2232; 
lean_dec(x_1522);
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
x_2232 = !lean_is_exclusive(x_1523);
if (x_2232 == 0)
{
return x_1523;
}
else
{
lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; 
x_2233 = lean_ctor_get(x_1523, 0);
x_2234 = lean_ctor_get(x_1523, 1);
lean_inc(x_2234);
lean_inc(x_2233);
lean_dec(x_1523);
x_2235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2235, 0, x_2233);
lean_ctor_set(x_2235, 1, x_2234);
return x_2235;
}
}
}
default: 
{
lean_object* x_2236; uint8_t x_2237; lean_object* x_2238; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_2236 = x_11;
} else {
 lean_dec_ref(x_11);
 x_2236 = lean_box(0);
}
x_2237 = 0;
lean_inc(x_33);
x_2238 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_2237, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_2238) == 0)
{
lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; uint8_t x_2564; 
x_2239 = lean_ctor_get(x_2238, 0);
lean_inc(x_2239);
x_2240 = lean_ctor_get(x_2238, 1);
lean_inc(x_2240);
lean_dec(x_2238);
x_2564 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2564 == 0)
{
lean_object* x_2565; 
x_2565 = lean_box(0);
x_2241 = x_2565;
goto block_2563;
}
else
{
uint8_t x_2566; 
x_2566 = lean_nat_dec_eq(x_24, x_27);
if (x_2566 == 0)
{
lean_object* x_2567; 
x_2567 = lean_box(0);
x_2241 = x_2567;
goto block_2563;
}
else
{
lean_object* x_2568; lean_object* x_2569; lean_object* x_2570; 
lean_dec(x_2236);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_2568 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2240);
x_2569 = lean_ctor_get(x_2568, 1);
lean_inc(x_2569);
lean_dec(x_2568);
x_2570 = l_Lean_Compiler_LCNF_Simp_simp(x_2239, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2569);
if (lean_obj_tag(x_2570) == 0)
{
uint8_t x_2571; 
x_2571 = !lean_is_exclusive(x_2570);
if (x_2571 == 0)
{
lean_object* x_2572; lean_object* x_2573; 
x_2572 = lean_ctor_get(x_2570, 0);
x_2573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2573, 0, x_2572);
lean_ctor_set(x_2570, 0, x_2573);
return x_2570;
}
else
{
lean_object* x_2574; lean_object* x_2575; lean_object* x_2576; lean_object* x_2577; 
x_2574 = lean_ctor_get(x_2570, 0);
x_2575 = lean_ctor_get(x_2570, 1);
lean_inc(x_2575);
lean_inc(x_2574);
lean_dec(x_2570);
x_2576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2576, 0, x_2574);
x_2577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2577, 0, x_2576);
lean_ctor_set(x_2577, 1, x_2575);
return x_2577;
}
}
else
{
uint8_t x_2578; 
x_2578 = !lean_is_exclusive(x_2570);
if (x_2578 == 0)
{
return x_2570;
}
else
{
lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; 
x_2579 = lean_ctor_get(x_2570, 0);
x_2580 = lean_ctor_get(x_2570, 1);
lean_inc(x_2580);
lean_inc(x_2579);
lean_dec(x_2570);
x_2581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2581, 0, x_2579);
lean_ctor_set(x_2581, 1, x_2580);
return x_2581;
}
}
}
}
block_2563:
{
lean_object* x_2242; 
lean_dec(x_2241);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2242 = l_Lean_Compiler_LCNF_Simp_simp(x_2239, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2240);
if (lean_obj_tag(x_2242) == 0)
{
lean_object* x_2243; lean_object* x_2244; uint8_t x_2245; 
x_2243 = lean_ctor_get(x_2242, 0);
lean_inc(x_2243);
x_2244 = lean_ctor_get(x_2242, 1);
lean_inc(x_2244);
lean_dec(x_2242);
lean_inc(x_2243);
x_2245 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_2243);
if (x_2245 == 0)
{
lean_object* x_2246; lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; uint8_t x_2250; 
x_2246 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2244);
x_2247 = lean_ctor_get(x_2246, 1);
lean_inc(x_2247);
lean_dec(x_2246);
x_2248 = lean_ctor_get(x_21, 2);
lean_inc(x_2248);
lean_dec(x_21);
x_2249 = l_Lean_Compiler_LCNF_inferAppType(x_2248, x_33, x_6, x_7, x_8, x_9, x_2247);
x_2250 = !lean_is_exclusive(x_2249);
if (x_2250 == 0)
{
lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; uint8_t x_2254; 
x_2251 = lean_ctor_get(x_2249, 0);
x_2252 = lean_ctor_get(x_2249, 1);
lean_inc(x_2251);
x_2253 = l_Lean_Expr_headBeta(x_2251);
x_2254 = l_Lean_Expr_isForall(x_2253);
lean_dec(x_2253);
if (x_2254 == 0)
{
lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; uint8_t x_2260; lean_object* x_2261; lean_object* x_2262; 
x_2255 = l_Lean_Compiler_LCNF_mkAuxParam(x_2251, x_2237, x_6, x_7, x_8, x_9, x_2252);
x_2256 = lean_ctor_get(x_2255, 0);
lean_inc(x_2256);
x_2257 = lean_ctor_get(x_2255, 1);
lean_inc(x_2257);
if (lean_is_exclusive(x_2255)) {
 lean_ctor_release(x_2255, 0);
 lean_ctor_release(x_2255, 1);
 x_2258 = x_2255;
} else {
 lean_dec_ref(x_2255);
 x_2258 = lean_box(0);
}
x_2259 = lean_ctor_get(x_2256, 0);
lean_inc(x_2259);
x_2260 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2260 == 0)
{
lean_object* x_2289; 
lean_free_object(x_2249);
lean_dec(x_2236);
lean_dec(x_27);
lean_dec(x_23);
x_2289 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2259, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2257);
if (lean_obj_tag(x_2289) == 0)
{
lean_object* x_2290; lean_object* x_2291; 
x_2290 = lean_ctor_get(x_2289, 1);
lean_inc(x_2290);
lean_dec(x_2289);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2291 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2290);
if (lean_obj_tag(x_2291) == 0)
{
lean_object* x_2292; lean_object* x_2293; 
x_2292 = lean_ctor_get(x_2291, 0);
lean_inc(x_2292);
x_2293 = lean_ctor_get(x_2291, 1);
lean_inc(x_2293);
lean_dec(x_2291);
x_2261 = x_2292;
x_2262 = x_2293;
goto block_2288;
}
else
{
uint8_t x_2294; 
lean_dec(x_2258);
lean_dec(x_2256);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2294 = !lean_is_exclusive(x_2291);
if (x_2294 == 0)
{
return x_2291;
}
else
{
lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; 
x_2295 = lean_ctor_get(x_2291, 0);
x_2296 = lean_ctor_get(x_2291, 1);
lean_inc(x_2296);
lean_inc(x_2295);
lean_dec(x_2291);
x_2297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2297, 0, x_2295);
lean_ctor_set(x_2297, 1, x_2296);
return x_2297;
}
}
}
else
{
uint8_t x_2298; 
lean_dec(x_2258);
lean_dec(x_2256);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2298 = !lean_is_exclusive(x_2289);
if (x_2298 == 0)
{
return x_2289;
}
else
{
lean_object* x_2299; lean_object* x_2300; lean_object* x_2301; 
x_2299 = lean_ctor_get(x_2289, 0);
x_2300 = lean_ctor_get(x_2289, 1);
lean_inc(x_2300);
lean_inc(x_2299);
lean_dec(x_2289);
x_2301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2301, 0, x_2299);
lean_ctor_set(x_2301, 1, x_2300);
return x_2301;
}
}
}
else
{
lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; 
x_2302 = lean_array_get_size(x_23);
x_2303 = l_Array_toSubarray___rarg(x_23, x_27, x_2302);
x_2304 = l_Array_ofSubarray___rarg(x_2303);
lean_dec(x_2303);
if (lean_is_scalar(x_2236)) {
 x_2305 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2305 = x_2236;
}
lean_ctor_set(x_2305, 0, x_2259);
lean_ctor_set(x_2305, 1, x_2304);
x_2306 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2307 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2305, x_2306, x_6, x_7, x_8, x_9, x_2257);
if (lean_obj_tag(x_2307) == 0)
{
lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; 
x_2308 = lean_ctor_get(x_2307, 0);
lean_inc(x_2308);
x_2309 = lean_ctor_get(x_2307, 1);
lean_inc(x_2309);
lean_dec(x_2307);
x_2310 = lean_ctor_get(x_2308, 0);
lean_inc(x_2310);
x_2311 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2310, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2309);
if (lean_obj_tag(x_2311) == 0)
{
lean_object* x_2312; lean_object* x_2313; 
x_2312 = lean_ctor_get(x_2311, 1);
lean_inc(x_2312);
lean_dec(x_2311);
lean_ctor_set(x_2249, 1, x_2);
lean_ctor_set(x_2249, 0, x_2308);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2313 = l_Lean_Compiler_LCNF_Simp_simp(x_2249, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2312);
if (lean_obj_tag(x_2313) == 0)
{
lean_object* x_2314; lean_object* x_2315; 
x_2314 = lean_ctor_get(x_2313, 0);
lean_inc(x_2314);
x_2315 = lean_ctor_get(x_2313, 1);
lean_inc(x_2315);
lean_dec(x_2313);
x_2261 = x_2314;
x_2262 = x_2315;
goto block_2288;
}
else
{
uint8_t x_2316; 
lean_dec(x_2258);
lean_dec(x_2256);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2316 = !lean_is_exclusive(x_2313);
if (x_2316 == 0)
{
return x_2313;
}
else
{
lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; 
x_2317 = lean_ctor_get(x_2313, 0);
x_2318 = lean_ctor_get(x_2313, 1);
lean_inc(x_2318);
lean_inc(x_2317);
lean_dec(x_2313);
x_2319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2319, 0, x_2317);
lean_ctor_set(x_2319, 1, x_2318);
return x_2319;
}
}
}
else
{
uint8_t x_2320; 
lean_dec(x_2308);
lean_dec(x_2258);
lean_dec(x_2256);
lean_free_object(x_2249);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2320 = !lean_is_exclusive(x_2311);
if (x_2320 == 0)
{
return x_2311;
}
else
{
lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; 
x_2321 = lean_ctor_get(x_2311, 0);
x_2322 = lean_ctor_get(x_2311, 1);
lean_inc(x_2322);
lean_inc(x_2321);
lean_dec(x_2311);
x_2323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2323, 0, x_2321);
lean_ctor_set(x_2323, 1, x_2322);
return x_2323;
}
}
}
else
{
uint8_t x_2324; 
lean_dec(x_2258);
lean_dec(x_2256);
lean_free_object(x_2249);
lean_dec(x_2243);
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
x_2324 = !lean_is_exclusive(x_2307);
if (x_2324 == 0)
{
return x_2307;
}
else
{
lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; 
x_2325 = lean_ctor_get(x_2307, 0);
x_2326 = lean_ctor_get(x_2307, 1);
lean_inc(x_2326);
lean_inc(x_2325);
lean_dec(x_2307);
x_2327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2327, 0, x_2325);
lean_ctor_set(x_2327, 1, x_2326);
return x_2327;
}
}
}
block_2288:
{
lean_object* x_2263; lean_object* x_2264; lean_object* x_2265; lean_object* x_2266; 
x_2263 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2264 = lean_array_push(x_2263, x_2256);
x_2265 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_2266 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2264, x_2261, x_2265, x_6, x_7, x_8, x_9, x_2262);
if (lean_obj_tag(x_2266) == 0)
{
lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; lean_object* x_2270; 
x_2267 = lean_ctor_get(x_2266, 0);
lean_inc(x_2267);
x_2268 = lean_ctor_get(x_2266, 1);
lean_inc(x_2268);
lean_dec(x_2266);
lean_inc(x_2267);
x_2269 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_2269, 0, x_2267);
lean_closure_set(x_2269, 1, x_2263);
x_2270 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2243, x_2269, x_6, x_7, x_8, x_9, x_2268);
if (lean_obj_tag(x_2270) == 0)
{
uint8_t x_2271; 
x_2271 = !lean_is_exclusive(x_2270);
if (x_2271 == 0)
{
lean_object* x_2272; lean_object* x_2273; lean_object* x_2274; 
x_2272 = lean_ctor_get(x_2270, 0);
if (lean_is_scalar(x_2258)) {
 x_2273 = lean_alloc_ctor(2, 2, 0);
} else {
 x_2273 = x_2258;
 lean_ctor_set_tag(x_2273, 2);
}
lean_ctor_set(x_2273, 0, x_2267);
lean_ctor_set(x_2273, 1, x_2272);
if (lean_is_scalar(x_22)) {
 x_2274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2274 = x_22;
}
lean_ctor_set(x_2274, 0, x_2273);
lean_ctor_set(x_2270, 0, x_2274);
return x_2270;
}
else
{
lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; 
x_2275 = lean_ctor_get(x_2270, 0);
x_2276 = lean_ctor_get(x_2270, 1);
lean_inc(x_2276);
lean_inc(x_2275);
lean_dec(x_2270);
if (lean_is_scalar(x_2258)) {
 x_2277 = lean_alloc_ctor(2, 2, 0);
} else {
 x_2277 = x_2258;
 lean_ctor_set_tag(x_2277, 2);
}
lean_ctor_set(x_2277, 0, x_2267);
lean_ctor_set(x_2277, 1, x_2275);
if (lean_is_scalar(x_22)) {
 x_2278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2278 = x_22;
}
lean_ctor_set(x_2278, 0, x_2277);
x_2279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2279, 0, x_2278);
lean_ctor_set(x_2279, 1, x_2276);
return x_2279;
}
}
else
{
uint8_t x_2280; 
lean_dec(x_2267);
lean_dec(x_2258);
lean_dec(x_22);
x_2280 = !lean_is_exclusive(x_2270);
if (x_2280 == 0)
{
return x_2270;
}
else
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; 
x_2281 = lean_ctor_get(x_2270, 0);
x_2282 = lean_ctor_get(x_2270, 1);
lean_inc(x_2282);
lean_inc(x_2281);
lean_dec(x_2270);
x_2283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2283, 0, x_2281);
lean_ctor_set(x_2283, 1, x_2282);
return x_2283;
}
}
}
else
{
uint8_t x_2284; 
lean_dec(x_2258);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2284 = !lean_is_exclusive(x_2266);
if (x_2284 == 0)
{
return x_2266;
}
else
{
lean_object* x_2285; lean_object* x_2286; lean_object* x_2287; 
x_2285 = lean_ctor_get(x_2266, 0);
x_2286 = lean_ctor_get(x_2266, 1);
lean_inc(x_2286);
lean_inc(x_2285);
lean_dec(x_2266);
x_2287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2287, 0, x_2285);
lean_ctor_set(x_2287, 1, x_2286);
return x_2287;
}
}
}
}
else
{
lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; 
lean_dec(x_2251);
x_2328 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2329 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_2330 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2328, x_2243, x_2329, x_6, x_7, x_8, x_9, x_2252);
if (lean_obj_tag(x_2330) == 0)
{
lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; 
x_2331 = lean_ctor_get(x_2330, 0);
lean_inc(x_2331);
x_2332 = lean_ctor_get(x_2330, 1);
lean_inc(x_2332);
lean_dec(x_2330);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2333 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2331, x_6, x_7, x_8, x_9, x_2332);
if (lean_obj_tag(x_2333) == 0)
{
lean_object* x_2334; lean_object* x_2335; lean_object* x_2336; uint8_t x_2337; lean_object* x_2338; lean_object* x_2339; 
x_2334 = lean_ctor_get(x_2333, 0);
lean_inc(x_2334);
x_2335 = lean_ctor_get(x_2333, 1);
lean_inc(x_2335);
lean_dec(x_2333);
x_2336 = lean_ctor_get(x_2334, 0);
lean_inc(x_2336);
x_2337 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2337 == 0)
{
lean_object* x_2352; 
lean_free_object(x_2249);
lean_dec(x_2236);
lean_dec(x_27);
lean_dec(x_23);
x_2352 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2336, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2335);
if (lean_obj_tag(x_2352) == 0)
{
lean_object* x_2353; lean_object* x_2354; 
x_2353 = lean_ctor_get(x_2352, 1);
lean_inc(x_2353);
lean_dec(x_2352);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2354 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2353);
if (lean_obj_tag(x_2354) == 0)
{
lean_object* x_2355; lean_object* x_2356; 
x_2355 = lean_ctor_get(x_2354, 0);
lean_inc(x_2355);
x_2356 = lean_ctor_get(x_2354, 1);
lean_inc(x_2356);
lean_dec(x_2354);
x_2338 = x_2355;
x_2339 = x_2356;
goto block_2351;
}
else
{
uint8_t x_2357; 
lean_dec(x_2334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2357 = !lean_is_exclusive(x_2354);
if (x_2357 == 0)
{
return x_2354;
}
else
{
lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; 
x_2358 = lean_ctor_get(x_2354, 0);
x_2359 = lean_ctor_get(x_2354, 1);
lean_inc(x_2359);
lean_inc(x_2358);
lean_dec(x_2354);
x_2360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2360, 0, x_2358);
lean_ctor_set(x_2360, 1, x_2359);
return x_2360;
}
}
}
else
{
uint8_t x_2361; 
lean_dec(x_2334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2361 = !lean_is_exclusive(x_2352);
if (x_2361 == 0)
{
return x_2352;
}
else
{
lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; 
x_2362 = lean_ctor_get(x_2352, 0);
x_2363 = lean_ctor_get(x_2352, 1);
lean_inc(x_2363);
lean_inc(x_2362);
lean_dec(x_2352);
x_2364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2364, 0, x_2362);
lean_ctor_set(x_2364, 1, x_2363);
return x_2364;
}
}
}
else
{
lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; 
x_2365 = lean_array_get_size(x_23);
x_2366 = l_Array_toSubarray___rarg(x_23, x_27, x_2365);
x_2367 = l_Array_ofSubarray___rarg(x_2366);
lean_dec(x_2366);
if (lean_is_scalar(x_2236)) {
 x_2368 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2368 = x_2236;
}
lean_ctor_set(x_2368, 0, x_2336);
lean_ctor_set(x_2368, 1, x_2367);
x_2369 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2370 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2368, x_2369, x_6, x_7, x_8, x_9, x_2335);
if (lean_obj_tag(x_2370) == 0)
{
lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; 
x_2371 = lean_ctor_get(x_2370, 0);
lean_inc(x_2371);
x_2372 = lean_ctor_get(x_2370, 1);
lean_inc(x_2372);
lean_dec(x_2370);
x_2373 = lean_ctor_get(x_2371, 0);
lean_inc(x_2373);
x_2374 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2373, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2372);
if (lean_obj_tag(x_2374) == 0)
{
lean_object* x_2375; lean_object* x_2376; 
x_2375 = lean_ctor_get(x_2374, 1);
lean_inc(x_2375);
lean_dec(x_2374);
lean_ctor_set(x_2249, 1, x_2);
lean_ctor_set(x_2249, 0, x_2371);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2376 = l_Lean_Compiler_LCNF_Simp_simp(x_2249, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2375);
if (lean_obj_tag(x_2376) == 0)
{
lean_object* x_2377; lean_object* x_2378; 
x_2377 = lean_ctor_get(x_2376, 0);
lean_inc(x_2377);
x_2378 = lean_ctor_get(x_2376, 1);
lean_inc(x_2378);
lean_dec(x_2376);
x_2338 = x_2377;
x_2339 = x_2378;
goto block_2351;
}
else
{
uint8_t x_2379; 
lean_dec(x_2334);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2379 = !lean_is_exclusive(x_2376);
if (x_2379 == 0)
{
return x_2376;
}
else
{
lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; 
x_2380 = lean_ctor_get(x_2376, 0);
x_2381 = lean_ctor_get(x_2376, 1);
lean_inc(x_2381);
lean_inc(x_2380);
lean_dec(x_2376);
x_2382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2382, 0, x_2380);
lean_ctor_set(x_2382, 1, x_2381);
return x_2382;
}
}
}
else
{
uint8_t x_2383; 
lean_dec(x_2371);
lean_dec(x_2334);
lean_free_object(x_2249);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2383 = !lean_is_exclusive(x_2374);
if (x_2383 == 0)
{
return x_2374;
}
else
{
lean_object* x_2384; lean_object* x_2385; lean_object* x_2386; 
x_2384 = lean_ctor_get(x_2374, 0);
x_2385 = lean_ctor_get(x_2374, 1);
lean_inc(x_2385);
lean_inc(x_2384);
lean_dec(x_2374);
x_2386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2386, 0, x_2384);
lean_ctor_set(x_2386, 1, x_2385);
return x_2386;
}
}
}
else
{
uint8_t x_2387; 
lean_dec(x_2334);
lean_free_object(x_2249);
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
x_2387 = !lean_is_exclusive(x_2370);
if (x_2387 == 0)
{
return x_2370;
}
else
{
lean_object* x_2388; lean_object* x_2389; lean_object* x_2390; 
x_2388 = lean_ctor_get(x_2370, 0);
x_2389 = lean_ctor_get(x_2370, 1);
lean_inc(x_2389);
lean_inc(x_2388);
lean_dec(x_2370);
x_2390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2390, 0, x_2388);
lean_ctor_set(x_2390, 1, x_2389);
return x_2390;
}
}
}
block_2351:
{
lean_object* x_2340; lean_object* x_2341; lean_object* x_2342; lean_object* x_2343; uint8_t x_2344; 
x_2340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2340, 0, x_2334);
x_2341 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2342 = lean_array_push(x_2341, x_2340);
x_2343 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2342, x_2338, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2339);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2342);
x_2344 = !lean_is_exclusive(x_2343);
if (x_2344 == 0)
{
lean_object* x_2345; lean_object* x_2346; 
x_2345 = lean_ctor_get(x_2343, 0);
if (lean_is_scalar(x_22)) {
 x_2346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2346 = x_22;
}
lean_ctor_set(x_2346, 0, x_2345);
lean_ctor_set(x_2343, 0, x_2346);
return x_2343;
}
else
{
lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; 
x_2347 = lean_ctor_get(x_2343, 0);
x_2348 = lean_ctor_get(x_2343, 1);
lean_inc(x_2348);
lean_inc(x_2347);
lean_dec(x_2343);
if (lean_is_scalar(x_22)) {
 x_2349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2349 = x_22;
}
lean_ctor_set(x_2349, 0, x_2347);
x_2350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2350, 0, x_2349);
lean_ctor_set(x_2350, 1, x_2348);
return x_2350;
}
}
}
else
{
uint8_t x_2391; 
lean_free_object(x_2249);
lean_dec(x_2236);
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
x_2391 = !lean_is_exclusive(x_2333);
if (x_2391 == 0)
{
return x_2333;
}
else
{
lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; 
x_2392 = lean_ctor_get(x_2333, 0);
x_2393 = lean_ctor_get(x_2333, 1);
lean_inc(x_2393);
lean_inc(x_2392);
lean_dec(x_2333);
x_2394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2394, 0, x_2392);
lean_ctor_set(x_2394, 1, x_2393);
return x_2394;
}
}
}
else
{
uint8_t x_2395; 
lean_free_object(x_2249);
lean_dec(x_2236);
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
x_2395 = !lean_is_exclusive(x_2330);
if (x_2395 == 0)
{
return x_2330;
}
else
{
lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; 
x_2396 = lean_ctor_get(x_2330, 0);
x_2397 = lean_ctor_get(x_2330, 1);
lean_inc(x_2397);
lean_inc(x_2396);
lean_dec(x_2330);
x_2398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2398, 0, x_2396);
lean_ctor_set(x_2398, 1, x_2397);
return x_2398;
}
}
}
}
else
{
lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; uint8_t x_2402; 
x_2399 = lean_ctor_get(x_2249, 0);
x_2400 = lean_ctor_get(x_2249, 1);
lean_inc(x_2400);
lean_inc(x_2399);
lean_dec(x_2249);
lean_inc(x_2399);
x_2401 = l_Lean_Expr_headBeta(x_2399);
x_2402 = l_Lean_Expr_isForall(x_2401);
lean_dec(x_2401);
if (x_2402 == 0)
{
lean_object* x_2403; lean_object* x_2404; lean_object* x_2405; lean_object* x_2406; lean_object* x_2407; uint8_t x_2408; lean_object* x_2409; lean_object* x_2410; 
x_2403 = l_Lean_Compiler_LCNF_mkAuxParam(x_2399, x_2237, x_6, x_7, x_8, x_9, x_2400);
x_2404 = lean_ctor_get(x_2403, 0);
lean_inc(x_2404);
x_2405 = lean_ctor_get(x_2403, 1);
lean_inc(x_2405);
if (lean_is_exclusive(x_2403)) {
 lean_ctor_release(x_2403, 0);
 lean_ctor_release(x_2403, 1);
 x_2406 = x_2403;
} else {
 lean_dec_ref(x_2403);
 x_2406 = lean_box(0);
}
x_2407 = lean_ctor_get(x_2404, 0);
lean_inc(x_2407);
x_2408 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2408 == 0)
{
lean_object* x_2434; 
lean_dec(x_2236);
lean_dec(x_27);
lean_dec(x_23);
x_2434 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2407, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2405);
if (lean_obj_tag(x_2434) == 0)
{
lean_object* x_2435; lean_object* x_2436; 
x_2435 = lean_ctor_get(x_2434, 1);
lean_inc(x_2435);
lean_dec(x_2434);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2436 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2435);
if (lean_obj_tag(x_2436) == 0)
{
lean_object* x_2437; lean_object* x_2438; 
x_2437 = lean_ctor_get(x_2436, 0);
lean_inc(x_2437);
x_2438 = lean_ctor_get(x_2436, 1);
lean_inc(x_2438);
lean_dec(x_2436);
x_2409 = x_2437;
x_2410 = x_2438;
goto block_2433;
}
else
{
lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; 
lean_dec(x_2406);
lean_dec(x_2404);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2439 = lean_ctor_get(x_2436, 0);
lean_inc(x_2439);
x_2440 = lean_ctor_get(x_2436, 1);
lean_inc(x_2440);
if (lean_is_exclusive(x_2436)) {
 lean_ctor_release(x_2436, 0);
 lean_ctor_release(x_2436, 1);
 x_2441 = x_2436;
} else {
 lean_dec_ref(x_2436);
 x_2441 = lean_box(0);
}
if (lean_is_scalar(x_2441)) {
 x_2442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2442 = x_2441;
}
lean_ctor_set(x_2442, 0, x_2439);
lean_ctor_set(x_2442, 1, x_2440);
return x_2442;
}
}
else
{
lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; 
lean_dec(x_2406);
lean_dec(x_2404);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2443 = lean_ctor_get(x_2434, 0);
lean_inc(x_2443);
x_2444 = lean_ctor_get(x_2434, 1);
lean_inc(x_2444);
if (lean_is_exclusive(x_2434)) {
 lean_ctor_release(x_2434, 0);
 lean_ctor_release(x_2434, 1);
 x_2445 = x_2434;
} else {
 lean_dec_ref(x_2434);
 x_2445 = lean_box(0);
}
if (lean_is_scalar(x_2445)) {
 x_2446 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2446 = x_2445;
}
lean_ctor_set(x_2446, 0, x_2443);
lean_ctor_set(x_2446, 1, x_2444);
return x_2446;
}
}
else
{
lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; lean_object* x_2452; 
x_2447 = lean_array_get_size(x_23);
x_2448 = l_Array_toSubarray___rarg(x_23, x_27, x_2447);
x_2449 = l_Array_ofSubarray___rarg(x_2448);
lean_dec(x_2448);
if (lean_is_scalar(x_2236)) {
 x_2450 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2450 = x_2236;
}
lean_ctor_set(x_2450, 0, x_2407);
lean_ctor_set(x_2450, 1, x_2449);
x_2451 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2452 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2450, x_2451, x_6, x_7, x_8, x_9, x_2405);
if (lean_obj_tag(x_2452) == 0)
{
lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; 
x_2453 = lean_ctor_get(x_2452, 0);
lean_inc(x_2453);
x_2454 = lean_ctor_get(x_2452, 1);
lean_inc(x_2454);
lean_dec(x_2452);
x_2455 = lean_ctor_get(x_2453, 0);
lean_inc(x_2455);
x_2456 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2455, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2454);
if (lean_obj_tag(x_2456) == 0)
{
lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; 
x_2457 = lean_ctor_get(x_2456, 1);
lean_inc(x_2457);
lean_dec(x_2456);
x_2458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2458, 0, x_2453);
lean_ctor_set(x_2458, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2459 = l_Lean_Compiler_LCNF_Simp_simp(x_2458, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2457);
if (lean_obj_tag(x_2459) == 0)
{
lean_object* x_2460; lean_object* x_2461; 
x_2460 = lean_ctor_get(x_2459, 0);
lean_inc(x_2460);
x_2461 = lean_ctor_get(x_2459, 1);
lean_inc(x_2461);
lean_dec(x_2459);
x_2409 = x_2460;
x_2410 = x_2461;
goto block_2433;
}
else
{
lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; 
lean_dec(x_2406);
lean_dec(x_2404);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2462 = lean_ctor_get(x_2459, 0);
lean_inc(x_2462);
x_2463 = lean_ctor_get(x_2459, 1);
lean_inc(x_2463);
if (lean_is_exclusive(x_2459)) {
 lean_ctor_release(x_2459, 0);
 lean_ctor_release(x_2459, 1);
 x_2464 = x_2459;
} else {
 lean_dec_ref(x_2459);
 x_2464 = lean_box(0);
}
if (lean_is_scalar(x_2464)) {
 x_2465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2465 = x_2464;
}
lean_ctor_set(x_2465, 0, x_2462);
lean_ctor_set(x_2465, 1, x_2463);
return x_2465;
}
}
else
{
lean_object* x_2466; lean_object* x_2467; lean_object* x_2468; lean_object* x_2469; 
lean_dec(x_2453);
lean_dec(x_2406);
lean_dec(x_2404);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2466 = lean_ctor_get(x_2456, 0);
lean_inc(x_2466);
x_2467 = lean_ctor_get(x_2456, 1);
lean_inc(x_2467);
if (lean_is_exclusive(x_2456)) {
 lean_ctor_release(x_2456, 0);
 lean_ctor_release(x_2456, 1);
 x_2468 = x_2456;
} else {
 lean_dec_ref(x_2456);
 x_2468 = lean_box(0);
}
if (lean_is_scalar(x_2468)) {
 x_2469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2469 = x_2468;
}
lean_ctor_set(x_2469, 0, x_2466);
lean_ctor_set(x_2469, 1, x_2467);
return x_2469;
}
}
else
{
lean_object* x_2470; lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; 
lean_dec(x_2406);
lean_dec(x_2404);
lean_dec(x_2243);
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
x_2470 = lean_ctor_get(x_2452, 0);
lean_inc(x_2470);
x_2471 = lean_ctor_get(x_2452, 1);
lean_inc(x_2471);
if (lean_is_exclusive(x_2452)) {
 lean_ctor_release(x_2452, 0);
 lean_ctor_release(x_2452, 1);
 x_2472 = x_2452;
} else {
 lean_dec_ref(x_2452);
 x_2472 = lean_box(0);
}
if (lean_is_scalar(x_2472)) {
 x_2473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2473 = x_2472;
}
lean_ctor_set(x_2473, 0, x_2470);
lean_ctor_set(x_2473, 1, x_2471);
return x_2473;
}
}
block_2433:
{
lean_object* x_2411; lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; 
x_2411 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2412 = lean_array_push(x_2411, x_2404);
x_2413 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__3;
x_2414 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2412, x_2409, x_2413, x_6, x_7, x_8, x_9, x_2410);
if (lean_obj_tag(x_2414) == 0)
{
lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; 
x_2415 = lean_ctor_get(x_2414, 0);
lean_inc(x_2415);
x_2416 = lean_ctor_get(x_2414, 1);
lean_inc(x_2416);
lean_dec(x_2414);
lean_inc(x_2415);
x_2417 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_2417, 0, x_2415);
lean_closure_set(x_2417, 1, x_2411);
x_2418 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2243, x_2417, x_6, x_7, x_8, x_9, x_2416);
if (lean_obj_tag(x_2418) == 0)
{
lean_object* x_2419; lean_object* x_2420; lean_object* x_2421; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; 
x_2419 = lean_ctor_get(x_2418, 0);
lean_inc(x_2419);
x_2420 = lean_ctor_get(x_2418, 1);
lean_inc(x_2420);
if (lean_is_exclusive(x_2418)) {
 lean_ctor_release(x_2418, 0);
 lean_ctor_release(x_2418, 1);
 x_2421 = x_2418;
} else {
 lean_dec_ref(x_2418);
 x_2421 = lean_box(0);
}
if (lean_is_scalar(x_2406)) {
 x_2422 = lean_alloc_ctor(2, 2, 0);
} else {
 x_2422 = x_2406;
 lean_ctor_set_tag(x_2422, 2);
}
lean_ctor_set(x_2422, 0, x_2415);
lean_ctor_set(x_2422, 1, x_2419);
if (lean_is_scalar(x_22)) {
 x_2423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2423 = x_22;
}
lean_ctor_set(x_2423, 0, x_2422);
if (lean_is_scalar(x_2421)) {
 x_2424 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2424 = x_2421;
}
lean_ctor_set(x_2424, 0, x_2423);
lean_ctor_set(x_2424, 1, x_2420);
return x_2424;
}
else
{
lean_object* x_2425; lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; 
lean_dec(x_2415);
lean_dec(x_2406);
lean_dec(x_22);
x_2425 = lean_ctor_get(x_2418, 0);
lean_inc(x_2425);
x_2426 = lean_ctor_get(x_2418, 1);
lean_inc(x_2426);
if (lean_is_exclusive(x_2418)) {
 lean_ctor_release(x_2418, 0);
 lean_ctor_release(x_2418, 1);
 x_2427 = x_2418;
} else {
 lean_dec_ref(x_2418);
 x_2427 = lean_box(0);
}
if (lean_is_scalar(x_2427)) {
 x_2428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2428 = x_2427;
}
lean_ctor_set(x_2428, 0, x_2425);
lean_ctor_set(x_2428, 1, x_2426);
return x_2428;
}
}
else
{
lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; 
lean_dec(x_2406);
lean_dec(x_2243);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_2429 = lean_ctor_get(x_2414, 0);
lean_inc(x_2429);
x_2430 = lean_ctor_get(x_2414, 1);
lean_inc(x_2430);
if (lean_is_exclusive(x_2414)) {
 lean_ctor_release(x_2414, 0);
 lean_ctor_release(x_2414, 1);
 x_2431 = x_2414;
} else {
 lean_dec_ref(x_2414);
 x_2431 = lean_box(0);
}
if (lean_is_scalar(x_2431)) {
 x_2432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2432 = x_2431;
}
lean_ctor_set(x_2432, 0, x_2429);
lean_ctor_set(x_2432, 1, x_2430);
return x_2432;
}
}
}
else
{
lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; 
lean_dec(x_2399);
x_2474 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_2475 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_2476 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_2474, x_2243, x_2475, x_6, x_7, x_8, x_9, x_2400);
if (lean_obj_tag(x_2476) == 0)
{
lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; 
x_2477 = lean_ctor_get(x_2476, 0);
lean_inc(x_2477);
x_2478 = lean_ctor_get(x_2476, 1);
lean_inc(x_2478);
lean_dec(x_2476);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2479 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_2477, x_6, x_7, x_8, x_9, x_2478);
if (lean_obj_tag(x_2479) == 0)
{
lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; uint8_t x_2483; lean_object* x_2484; lean_object* x_2485; 
x_2480 = lean_ctor_get(x_2479, 0);
lean_inc(x_2480);
x_2481 = lean_ctor_get(x_2479, 1);
lean_inc(x_2481);
lean_dec(x_2479);
x_2482 = lean_ctor_get(x_2480, 0);
lean_inc(x_2482);
x_2483 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_2483 == 0)
{
lean_object* x_2496; 
lean_dec(x_2236);
lean_dec(x_27);
lean_dec(x_23);
x_2496 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2482, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2481);
if (lean_obj_tag(x_2496) == 0)
{
lean_object* x_2497; lean_object* x_2498; 
x_2497 = lean_ctor_get(x_2496, 1);
lean_inc(x_2497);
lean_dec(x_2496);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2498 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2497);
if (lean_obj_tag(x_2498) == 0)
{
lean_object* x_2499; lean_object* x_2500; 
x_2499 = lean_ctor_get(x_2498, 0);
lean_inc(x_2499);
x_2500 = lean_ctor_get(x_2498, 1);
lean_inc(x_2500);
lean_dec(x_2498);
x_2484 = x_2499;
x_2485 = x_2500;
goto block_2495;
}
else
{
lean_object* x_2501; lean_object* x_2502; lean_object* x_2503; lean_object* x_2504; 
lean_dec(x_2480);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2501 = lean_ctor_get(x_2498, 0);
lean_inc(x_2501);
x_2502 = lean_ctor_get(x_2498, 1);
lean_inc(x_2502);
if (lean_is_exclusive(x_2498)) {
 lean_ctor_release(x_2498, 0);
 lean_ctor_release(x_2498, 1);
 x_2503 = x_2498;
} else {
 lean_dec_ref(x_2498);
 x_2503 = lean_box(0);
}
if (lean_is_scalar(x_2503)) {
 x_2504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2504 = x_2503;
}
lean_ctor_set(x_2504, 0, x_2501);
lean_ctor_set(x_2504, 1, x_2502);
return x_2504;
}
}
else
{
lean_object* x_2505; lean_object* x_2506; lean_object* x_2507; lean_object* x_2508; 
lean_dec(x_2480);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2505 = lean_ctor_get(x_2496, 0);
lean_inc(x_2505);
x_2506 = lean_ctor_get(x_2496, 1);
lean_inc(x_2506);
if (lean_is_exclusive(x_2496)) {
 lean_ctor_release(x_2496, 0);
 lean_ctor_release(x_2496, 1);
 x_2507 = x_2496;
} else {
 lean_dec_ref(x_2496);
 x_2507 = lean_box(0);
}
if (lean_is_scalar(x_2507)) {
 x_2508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2508 = x_2507;
}
lean_ctor_set(x_2508, 0, x_2505);
lean_ctor_set(x_2508, 1, x_2506);
return x_2508;
}
}
else
{
lean_object* x_2509; lean_object* x_2510; lean_object* x_2511; lean_object* x_2512; lean_object* x_2513; lean_object* x_2514; 
x_2509 = lean_array_get_size(x_23);
x_2510 = l_Array_toSubarray___rarg(x_23, x_27, x_2509);
x_2511 = l_Array_ofSubarray___rarg(x_2510);
lean_dec(x_2510);
if (lean_is_scalar(x_2236)) {
 x_2512 = lean_alloc_ctor(4, 2, 0);
} else {
 x_2512 = x_2236;
}
lean_ctor_set(x_2512, 0, x_2482);
lean_ctor_set(x_2512, 1, x_2511);
x_2513 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_2514 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_2512, x_2513, x_6, x_7, x_8, x_9, x_2481);
if (lean_obj_tag(x_2514) == 0)
{
lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; lean_object* x_2518; 
x_2515 = lean_ctor_get(x_2514, 0);
lean_inc(x_2515);
x_2516 = lean_ctor_get(x_2514, 1);
lean_inc(x_2516);
lean_dec(x_2514);
x_2517 = lean_ctor_get(x_2515, 0);
lean_inc(x_2517);
x_2518 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2517, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2516);
if (lean_obj_tag(x_2518) == 0)
{
lean_object* x_2519; lean_object* x_2520; lean_object* x_2521; 
x_2519 = lean_ctor_get(x_2518, 1);
lean_inc(x_2519);
lean_dec(x_2518);
x_2520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2520, 0, x_2515);
lean_ctor_set(x_2520, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_2521 = l_Lean_Compiler_LCNF_Simp_simp(x_2520, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2519);
if (lean_obj_tag(x_2521) == 0)
{
lean_object* x_2522; lean_object* x_2523; 
x_2522 = lean_ctor_get(x_2521, 0);
lean_inc(x_2522);
x_2523 = lean_ctor_get(x_2521, 1);
lean_inc(x_2523);
lean_dec(x_2521);
x_2484 = x_2522;
x_2485 = x_2523;
goto block_2495;
}
else
{
lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; 
lean_dec(x_2480);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_2524 = lean_ctor_get(x_2521, 0);
lean_inc(x_2524);
x_2525 = lean_ctor_get(x_2521, 1);
lean_inc(x_2525);
if (lean_is_exclusive(x_2521)) {
 lean_ctor_release(x_2521, 0);
 lean_ctor_release(x_2521, 1);
 x_2526 = x_2521;
} else {
 lean_dec_ref(x_2521);
 x_2526 = lean_box(0);
}
if (lean_is_scalar(x_2526)) {
 x_2527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2527 = x_2526;
}
lean_ctor_set(x_2527, 0, x_2524);
lean_ctor_set(x_2527, 1, x_2525);
return x_2527;
}
}
else
{
lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; 
lean_dec(x_2515);
lean_dec(x_2480);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2528 = lean_ctor_get(x_2518, 0);
lean_inc(x_2528);
x_2529 = lean_ctor_get(x_2518, 1);
lean_inc(x_2529);
if (lean_is_exclusive(x_2518)) {
 lean_ctor_release(x_2518, 0);
 lean_ctor_release(x_2518, 1);
 x_2530 = x_2518;
} else {
 lean_dec_ref(x_2518);
 x_2530 = lean_box(0);
}
if (lean_is_scalar(x_2530)) {
 x_2531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2531 = x_2530;
}
lean_ctor_set(x_2531, 0, x_2528);
lean_ctor_set(x_2531, 1, x_2529);
return x_2531;
}
}
else
{
lean_object* x_2532; lean_object* x_2533; lean_object* x_2534; lean_object* x_2535; 
lean_dec(x_2480);
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
x_2532 = lean_ctor_get(x_2514, 0);
lean_inc(x_2532);
x_2533 = lean_ctor_get(x_2514, 1);
lean_inc(x_2533);
if (lean_is_exclusive(x_2514)) {
 lean_ctor_release(x_2514, 0);
 lean_ctor_release(x_2514, 1);
 x_2534 = x_2514;
} else {
 lean_dec_ref(x_2514);
 x_2534 = lean_box(0);
}
if (lean_is_scalar(x_2534)) {
 x_2535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2535 = x_2534;
}
lean_ctor_set(x_2535, 0, x_2532);
lean_ctor_set(x_2535, 1, x_2533);
return x_2535;
}
}
block_2495:
{
lean_object* x_2486; lean_object* x_2487; lean_object* x_2488; lean_object* x_2489; lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; 
x_2486 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2486, 0, x_2480);
x_2487 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
x_2488 = lean_array_push(x_2487, x_2486);
x_2489 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_2488, x_2484, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2485);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2488);
x_2490 = lean_ctor_get(x_2489, 0);
lean_inc(x_2490);
x_2491 = lean_ctor_get(x_2489, 1);
lean_inc(x_2491);
if (lean_is_exclusive(x_2489)) {
 lean_ctor_release(x_2489, 0);
 lean_ctor_release(x_2489, 1);
 x_2492 = x_2489;
} else {
 lean_dec_ref(x_2489);
 x_2492 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2493 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2493 = x_22;
}
lean_ctor_set(x_2493, 0, x_2490);
if (lean_is_scalar(x_2492)) {
 x_2494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2494 = x_2492;
}
lean_ctor_set(x_2494, 0, x_2493);
lean_ctor_set(x_2494, 1, x_2491);
return x_2494;
}
}
else
{
lean_object* x_2536; lean_object* x_2537; lean_object* x_2538; lean_object* x_2539; 
lean_dec(x_2236);
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
x_2536 = lean_ctor_get(x_2479, 0);
lean_inc(x_2536);
x_2537 = lean_ctor_get(x_2479, 1);
lean_inc(x_2537);
if (lean_is_exclusive(x_2479)) {
 lean_ctor_release(x_2479, 0);
 lean_ctor_release(x_2479, 1);
 x_2538 = x_2479;
} else {
 lean_dec_ref(x_2479);
 x_2538 = lean_box(0);
}
if (lean_is_scalar(x_2538)) {
 x_2539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2539 = x_2538;
}
lean_ctor_set(x_2539, 0, x_2536);
lean_ctor_set(x_2539, 1, x_2537);
return x_2539;
}
}
else
{
lean_object* x_2540; lean_object* x_2541; lean_object* x_2542; lean_object* x_2543; 
lean_dec(x_2236);
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
x_2540 = lean_ctor_get(x_2476, 0);
lean_inc(x_2540);
x_2541 = lean_ctor_get(x_2476, 1);
lean_inc(x_2541);
if (lean_is_exclusive(x_2476)) {
 lean_ctor_release(x_2476, 0);
 lean_ctor_release(x_2476, 1);
 x_2542 = x_2476;
} else {
 lean_dec_ref(x_2476);
 x_2542 = lean_box(0);
}
if (lean_is_scalar(x_2542)) {
 x_2543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2543 = x_2542;
}
lean_ctor_set(x_2543, 0, x_2540);
lean_ctor_set(x_2543, 1, x_2541);
return x_2543;
}
}
}
}
else
{
lean_object* x_2544; lean_object* x_2545; lean_object* x_2546; lean_object* x_2547; 
lean_dec(x_2236);
lean_dec(x_33);
lean_dec(x_21);
x_2544 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2244);
x_2545 = lean_ctor_get(x_2544, 1);
lean_inc(x_2545);
lean_dec(x_2544);
x_2546 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_2546, 0, x_3);
lean_closure_set(x_2546, 1, x_4);
lean_closure_set(x_2546, 2, x_5);
lean_closure_set(x_2546, 3, x_27);
lean_closure_set(x_2546, 4, x_24);
lean_closure_set(x_2546, 5, x_26);
lean_closure_set(x_2546, 6, x_2);
lean_closure_set(x_2546, 7, x_23);
x_2547 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_2243, x_2546, x_6, x_7, x_8, x_9, x_2545);
if (lean_obj_tag(x_2547) == 0)
{
uint8_t x_2548; 
x_2548 = !lean_is_exclusive(x_2547);
if (x_2548 == 0)
{
lean_object* x_2549; lean_object* x_2550; 
x_2549 = lean_ctor_get(x_2547, 0);
if (lean_is_scalar(x_22)) {
 x_2550 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2550 = x_22;
}
lean_ctor_set(x_2550, 0, x_2549);
lean_ctor_set(x_2547, 0, x_2550);
return x_2547;
}
else
{
lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; lean_object* x_2554; 
x_2551 = lean_ctor_get(x_2547, 0);
x_2552 = lean_ctor_get(x_2547, 1);
lean_inc(x_2552);
lean_inc(x_2551);
lean_dec(x_2547);
if (lean_is_scalar(x_22)) {
 x_2553 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2553 = x_22;
}
lean_ctor_set(x_2553, 0, x_2551);
x_2554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2554, 0, x_2553);
lean_ctor_set(x_2554, 1, x_2552);
return x_2554;
}
}
else
{
uint8_t x_2555; 
lean_dec(x_22);
x_2555 = !lean_is_exclusive(x_2547);
if (x_2555 == 0)
{
return x_2547;
}
else
{
lean_object* x_2556; lean_object* x_2557; lean_object* x_2558; 
x_2556 = lean_ctor_get(x_2547, 0);
x_2557 = lean_ctor_get(x_2547, 1);
lean_inc(x_2557);
lean_inc(x_2556);
lean_dec(x_2547);
x_2558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2558, 0, x_2556);
lean_ctor_set(x_2558, 1, x_2557);
return x_2558;
}
}
}
}
else
{
uint8_t x_2559; 
lean_dec(x_2236);
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
x_2559 = !lean_is_exclusive(x_2242);
if (x_2559 == 0)
{
return x_2242;
}
else
{
lean_object* x_2560; lean_object* x_2561; lean_object* x_2562; 
x_2560 = lean_ctor_get(x_2242, 0);
x_2561 = lean_ctor_get(x_2242, 1);
lean_inc(x_2561);
lean_inc(x_2560);
lean_dec(x_2242);
x_2562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2562, 0, x_2560);
lean_ctor_set(x_2562, 1, x_2561);
return x_2562;
}
}
}
}
else
{
uint8_t x_2582; 
lean_dec(x_2236);
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
x_2582 = !lean_is_exclusive(x_2238);
if (x_2582 == 0)
{
return x_2238;
}
else
{
lean_object* x_2583; lean_object* x_2584; lean_object* x_2585; 
x_2583 = lean_ctor_get(x_2238, 0);
x_2584 = lean_ctor_get(x_2238, 1);
lean_inc(x_2584);
lean_inc(x_2583);
lean_dec(x_2238);
x_2585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2585, 0, x_2583);
lean_ctor_set(x_2585, 1, x_2584);
return x_2585;
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
lean_object* x_2586; lean_object* x_2587; 
x_2586 = lean_ctor_get(x_11, 0);
lean_inc(x_2586);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_2586);
x_2587 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_2586, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2587) == 0)
{
lean_object* x_2588; lean_object* x_2589; uint8_t x_2590; 
x_2588 = lean_ctor_get(x_2587, 0);
lean_inc(x_2588);
x_2589 = lean_ctor_get(x_2587, 1);
lean_inc(x_2589);
lean_dec(x_2587);
x_2590 = !lean_is_exclusive(x_3);
if (x_2590 == 0)
{
lean_object* x_2591; lean_object* x_2592; lean_object* x_2593; lean_object* x_2594; lean_object* x_2595; 
x_2591 = lean_ctor_get(x_3, 2);
x_2592 = lean_ctor_get(x_3, 3);
lean_inc(x_2586);
x_2593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2593, 0, x_2586);
lean_ctor_set(x_2593, 1, x_2591);
x_2594 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_2592, x_2586, x_2588);
lean_ctor_set(x_3, 3, x_2594);
lean_ctor_set(x_3, 2, x_2593);
x_2595 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2589);
if (lean_obj_tag(x_2595) == 0)
{
lean_object* x_2596; lean_object* x_2597; lean_object* x_2598; lean_object* x_2599; 
x_2596 = lean_ctor_get(x_2595, 0);
lean_inc(x_2596);
x_2597 = lean_ctor_get(x_2595, 1);
lean_inc(x_2597);
lean_dec(x_2595);
x_2598 = lean_ctor_get(x_2596, 0);
lean_inc(x_2598);
x_2599 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2598, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2597);
if (lean_obj_tag(x_2599) == 0)
{
lean_object* x_2600; lean_object* x_2601; uint8_t x_2602; 
x_2600 = lean_ctor_get(x_2599, 1);
lean_inc(x_2600);
lean_dec(x_2599);
x_2601 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2600);
x_2602 = !lean_is_exclusive(x_2601);
if (x_2602 == 0)
{
lean_object* x_2603; lean_object* x_2604; lean_object* x_2605; 
x_2603 = lean_ctor_get(x_2601, 1);
x_2604 = lean_ctor_get(x_2601, 0);
lean_dec(x_2604);
lean_ctor_set_tag(x_2601, 1);
lean_ctor_set(x_2601, 1, x_2);
lean_ctor_set(x_2601, 0, x_2596);
x_2605 = l_Lean_Compiler_LCNF_Simp_simp(x_2601, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2603);
if (lean_obj_tag(x_2605) == 0)
{
uint8_t x_2606; 
x_2606 = !lean_is_exclusive(x_2605);
if (x_2606 == 0)
{
lean_object* x_2607; lean_object* x_2608; 
x_2607 = lean_ctor_get(x_2605, 0);
if (lean_is_scalar(x_22)) {
 x_2608 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2608 = x_22;
}
lean_ctor_set(x_2608, 0, x_2607);
lean_ctor_set(x_2605, 0, x_2608);
return x_2605;
}
else
{
lean_object* x_2609; lean_object* x_2610; lean_object* x_2611; lean_object* x_2612; 
x_2609 = lean_ctor_get(x_2605, 0);
x_2610 = lean_ctor_get(x_2605, 1);
lean_inc(x_2610);
lean_inc(x_2609);
lean_dec(x_2605);
if (lean_is_scalar(x_22)) {
 x_2611 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2611 = x_22;
}
lean_ctor_set(x_2611, 0, x_2609);
x_2612 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2612, 0, x_2611);
lean_ctor_set(x_2612, 1, x_2610);
return x_2612;
}
}
else
{
uint8_t x_2613; 
lean_dec(x_22);
x_2613 = !lean_is_exclusive(x_2605);
if (x_2613 == 0)
{
return x_2605;
}
else
{
lean_object* x_2614; lean_object* x_2615; lean_object* x_2616; 
x_2614 = lean_ctor_get(x_2605, 0);
x_2615 = lean_ctor_get(x_2605, 1);
lean_inc(x_2615);
lean_inc(x_2614);
lean_dec(x_2605);
x_2616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2616, 0, x_2614);
lean_ctor_set(x_2616, 1, x_2615);
return x_2616;
}
}
}
else
{
lean_object* x_2617; lean_object* x_2618; lean_object* x_2619; 
x_2617 = lean_ctor_get(x_2601, 1);
lean_inc(x_2617);
lean_dec(x_2601);
x_2618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2618, 0, x_2596);
lean_ctor_set(x_2618, 1, x_2);
x_2619 = l_Lean_Compiler_LCNF_Simp_simp(x_2618, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2617);
if (lean_obj_tag(x_2619) == 0)
{
lean_object* x_2620; lean_object* x_2621; lean_object* x_2622; lean_object* x_2623; lean_object* x_2624; 
x_2620 = lean_ctor_get(x_2619, 0);
lean_inc(x_2620);
x_2621 = lean_ctor_get(x_2619, 1);
lean_inc(x_2621);
if (lean_is_exclusive(x_2619)) {
 lean_ctor_release(x_2619, 0);
 lean_ctor_release(x_2619, 1);
 x_2622 = x_2619;
} else {
 lean_dec_ref(x_2619);
 x_2622 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2623 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2623 = x_22;
}
lean_ctor_set(x_2623, 0, x_2620);
if (lean_is_scalar(x_2622)) {
 x_2624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2624 = x_2622;
}
lean_ctor_set(x_2624, 0, x_2623);
lean_ctor_set(x_2624, 1, x_2621);
return x_2624;
}
else
{
lean_object* x_2625; lean_object* x_2626; lean_object* x_2627; lean_object* x_2628; 
lean_dec(x_22);
x_2625 = lean_ctor_get(x_2619, 0);
lean_inc(x_2625);
x_2626 = lean_ctor_get(x_2619, 1);
lean_inc(x_2626);
if (lean_is_exclusive(x_2619)) {
 lean_ctor_release(x_2619, 0);
 lean_ctor_release(x_2619, 1);
 x_2627 = x_2619;
} else {
 lean_dec_ref(x_2619);
 x_2627 = lean_box(0);
}
if (lean_is_scalar(x_2627)) {
 x_2628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2628 = x_2627;
}
lean_ctor_set(x_2628, 0, x_2625);
lean_ctor_set(x_2628, 1, x_2626);
return x_2628;
}
}
}
else
{
uint8_t x_2629; 
lean_dec(x_2596);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2629 = !lean_is_exclusive(x_2599);
if (x_2629 == 0)
{
return x_2599;
}
else
{
lean_object* x_2630; lean_object* x_2631; lean_object* x_2632; 
x_2630 = lean_ctor_get(x_2599, 0);
x_2631 = lean_ctor_get(x_2599, 1);
lean_inc(x_2631);
lean_inc(x_2630);
lean_dec(x_2599);
x_2632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2632, 0, x_2630);
lean_ctor_set(x_2632, 1, x_2631);
return x_2632;
}
}
}
else
{
uint8_t x_2633; 
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
x_2633 = !lean_is_exclusive(x_2595);
if (x_2633 == 0)
{
return x_2595;
}
else
{
lean_object* x_2634; lean_object* x_2635; lean_object* x_2636; 
x_2634 = lean_ctor_get(x_2595, 0);
x_2635 = lean_ctor_get(x_2595, 1);
lean_inc(x_2635);
lean_inc(x_2634);
lean_dec(x_2595);
x_2636 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2636, 0, x_2634);
lean_ctor_set(x_2636, 1, x_2635);
return x_2636;
}
}
}
else
{
lean_object* x_2637; lean_object* x_2638; lean_object* x_2639; lean_object* x_2640; lean_object* x_2641; lean_object* x_2642; lean_object* x_2643; lean_object* x_2644; 
x_2637 = lean_ctor_get(x_3, 0);
x_2638 = lean_ctor_get(x_3, 1);
x_2639 = lean_ctor_get(x_3, 2);
x_2640 = lean_ctor_get(x_3, 3);
lean_inc(x_2640);
lean_inc(x_2639);
lean_inc(x_2638);
lean_inc(x_2637);
lean_dec(x_3);
lean_inc(x_2586);
x_2641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2641, 0, x_2586);
lean_ctor_set(x_2641, 1, x_2639);
x_2642 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Diagnostics_recordUnfold___spec__4(x_2640, x_2586, x_2588);
x_2643 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2643, 0, x_2637);
lean_ctor_set(x_2643, 1, x_2638);
lean_ctor_set(x_2643, 2, x_2641);
lean_ctor_set(x_2643, 3, x_2642);
x_2644 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_2643, x_4, x_5, x_6, x_7, x_8, x_9, x_2589);
if (lean_obj_tag(x_2644) == 0)
{
lean_object* x_2645; lean_object* x_2646; lean_object* x_2647; lean_object* x_2648; 
x_2645 = lean_ctor_get(x_2644, 0);
lean_inc(x_2645);
x_2646 = lean_ctor_get(x_2644, 1);
lean_inc(x_2646);
lean_dec(x_2644);
x_2647 = lean_ctor_get(x_2645, 0);
lean_inc(x_2647);
x_2648 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2647, x_2643, x_4, x_5, x_6, x_7, x_8, x_9, x_2646);
if (lean_obj_tag(x_2648) == 0)
{
lean_object* x_2649; lean_object* x_2650; lean_object* x_2651; lean_object* x_2652; lean_object* x_2653; lean_object* x_2654; 
x_2649 = lean_ctor_get(x_2648, 1);
lean_inc(x_2649);
lean_dec(x_2648);
x_2650 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2649);
x_2651 = lean_ctor_get(x_2650, 1);
lean_inc(x_2651);
if (lean_is_exclusive(x_2650)) {
 lean_ctor_release(x_2650, 0);
 lean_ctor_release(x_2650, 1);
 x_2652 = x_2650;
} else {
 lean_dec_ref(x_2650);
 x_2652 = lean_box(0);
}
if (lean_is_scalar(x_2652)) {
 x_2653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2653 = x_2652;
 lean_ctor_set_tag(x_2653, 1);
}
lean_ctor_set(x_2653, 0, x_2645);
lean_ctor_set(x_2653, 1, x_2);
x_2654 = l_Lean_Compiler_LCNF_Simp_simp(x_2653, x_2643, x_4, x_5, x_6, x_7, x_8, x_9, x_2651);
if (lean_obj_tag(x_2654) == 0)
{
lean_object* x_2655; lean_object* x_2656; lean_object* x_2657; lean_object* x_2658; lean_object* x_2659; 
x_2655 = lean_ctor_get(x_2654, 0);
lean_inc(x_2655);
x_2656 = lean_ctor_get(x_2654, 1);
lean_inc(x_2656);
if (lean_is_exclusive(x_2654)) {
 lean_ctor_release(x_2654, 0);
 lean_ctor_release(x_2654, 1);
 x_2657 = x_2654;
} else {
 lean_dec_ref(x_2654);
 x_2657 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2658 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2658 = x_22;
}
lean_ctor_set(x_2658, 0, x_2655);
if (lean_is_scalar(x_2657)) {
 x_2659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2659 = x_2657;
}
lean_ctor_set(x_2659, 0, x_2658);
lean_ctor_set(x_2659, 1, x_2656);
return x_2659;
}
else
{
lean_object* x_2660; lean_object* x_2661; lean_object* x_2662; lean_object* x_2663; 
lean_dec(x_22);
x_2660 = lean_ctor_get(x_2654, 0);
lean_inc(x_2660);
x_2661 = lean_ctor_get(x_2654, 1);
lean_inc(x_2661);
if (lean_is_exclusive(x_2654)) {
 lean_ctor_release(x_2654, 0);
 lean_ctor_release(x_2654, 1);
 x_2662 = x_2654;
} else {
 lean_dec_ref(x_2654);
 x_2662 = lean_box(0);
}
if (lean_is_scalar(x_2662)) {
 x_2663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2663 = x_2662;
}
lean_ctor_set(x_2663, 0, x_2660);
lean_ctor_set(x_2663, 1, x_2661);
return x_2663;
}
}
else
{
lean_object* x_2664; lean_object* x_2665; lean_object* x_2666; lean_object* x_2667; 
lean_dec(x_2645);
lean_dec(x_2643);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2664 = lean_ctor_get(x_2648, 0);
lean_inc(x_2664);
x_2665 = lean_ctor_get(x_2648, 1);
lean_inc(x_2665);
if (lean_is_exclusive(x_2648)) {
 lean_ctor_release(x_2648, 0);
 lean_ctor_release(x_2648, 1);
 x_2666 = x_2648;
} else {
 lean_dec_ref(x_2648);
 x_2666 = lean_box(0);
}
if (lean_is_scalar(x_2666)) {
 x_2667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2667 = x_2666;
}
lean_ctor_set(x_2667, 0, x_2664);
lean_ctor_set(x_2667, 1, x_2665);
return x_2667;
}
}
else
{
lean_object* x_2668; lean_object* x_2669; lean_object* x_2670; lean_object* x_2671; 
lean_dec(x_2643);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2668 = lean_ctor_get(x_2644, 0);
lean_inc(x_2668);
x_2669 = lean_ctor_get(x_2644, 1);
lean_inc(x_2669);
if (lean_is_exclusive(x_2644)) {
 lean_ctor_release(x_2644, 0);
 lean_ctor_release(x_2644, 1);
 x_2670 = x_2644;
} else {
 lean_dec_ref(x_2644);
 x_2670 = lean_box(0);
}
if (lean_is_scalar(x_2670)) {
 x_2671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2671 = x_2670;
}
lean_ctor_set(x_2671, 0, x_2668);
lean_ctor_set(x_2671, 1, x_2669);
return x_2671;
}
}
}
else
{
uint8_t x_2672; 
lean_dec(x_2586);
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
x_2672 = !lean_is_exclusive(x_2587);
if (x_2672 == 0)
{
return x_2587;
}
else
{
lean_object* x_2673; lean_object* x_2674; lean_object* x_2675; 
x_2673 = lean_ctor_get(x_2587, 0);
x_2674 = lean_ctor_get(x_2587, 1);
lean_inc(x_2674);
lean_inc(x_2673);
lean_dec(x_2587);
x_2675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2675, 0, x_2673);
lean_ctor_set(x_2675, 1, x_2674);
return x_2675;
}
}
}
else
{
lean_object* x_2676; 
lean_dec(x_11);
x_2676 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2676) == 0)
{
lean_object* x_2677; lean_object* x_2678; lean_object* x_2679; lean_object* x_2680; 
x_2677 = lean_ctor_get(x_2676, 0);
lean_inc(x_2677);
x_2678 = lean_ctor_get(x_2676, 1);
lean_inc(x_2678);
lean_dec(x_2676);
x_2679 = lean_ctor_get(x_2677, 0);
lean_inc(x_2679);
x_2680 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2679, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2678);
if (lean_obj_tag(x_2680) == 0)
{
lean_object* x_2681; lean_object* x_2682; uint8_t x_2683; 
x_2681 = lean_ctor_get(x_2680, 1);
lean_inc(x_2681);
lean_dec(x_2680);
x_2682 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2681);
x_2683 = !lean_is_exclusive(x_2682);
if (x_2683 == 0)
{
lean_object* x_2684; lean_object* x_2685; lean_object* x_2686; 
x_2684 = lean_ctor_get(x_2682, 1);
x_2685 = lean_ctor_get(x_2682, 0);
lean_dec(x_2685);
lean_ctor_set_tag(x_2682, 1);
lean_ctor_set(x_2682, 1, x_2);
lean_ctor_set(x_2682, 0, x_2677);
x_2686 = l_Lean_Compiler_LCNF_Simp_simp(x_2682, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2684);
if (lean_obj_tag(x_2686) == 0)
{
uint8_t x_2687; 
x_2687 = !lean_is_exclusive(x_2686);
if (x_2687 == 0)
{
lean_object* x_2688; lean_object* x_2689; 
x_2688 = lean_ctor_get(x_2686, 0);
if (lean_is_scalar(x_22)) {
 x_2689 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2689 = x_22;
}
lean_ctor_set(x_2689, 0, x_2688);
lean_ctor_set(x_2686, 0, x_2689);
return x_2686;
}
else
{
lean_object* x_2690; lean_object* x_2691; lean_object* x_2692; lean_object* x_2693; 
x_2690 = lean_ctor_get(x_2686, 0);
x_2691 = lean_ctor_get(x_2686, 1);
lean_inc(x_2691);
lean_inc(x_2690);
lean_dec(x_2686);
if (lean_is_scalar(x_22)) {
 x_2692 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2692 = x_22;
}
lean_ctor_set(x_2692, 0, x_2690);
x_2693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2693, 0, x_2692);
lean_ctor_set(x_2693, 1, x_2691);
return x_2693;
}
}
else
{
uint8_t x_2694; 
lean_dec(x_22);
x_2694 = !lean_is_exclusive(x_2686);
if (x_2694 == 0)
{
return x_2686;
}
else
{
lean_object* x_2695; lean_object* x_2696; lean_object* x_2697; 
x_2695 = lean_ctor_get(x_2686, 0);
x_2696 = lean_ctor_get(x_2686, 1);
lean_inc(x_2696);
lean_inc(x_2695);
lean_dec(x_2686);
x_2697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2697, 0, x_2695);
lean_ctor_set(x_2697, 1, x_2696);
return x_2697;
}
}
}
else
{
lean_object* x_2698; lean_object* x_2699; lean_object* x_2700; 
x_2698 = lean_ctor_get(x_2682, 1);
lean_inc(x_2698);
lean_dec(x_2682);
x_2699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2699, 0, x_2677);
lean_ctor_set(x_2699, 1, x_2);
x_2700 = l_Lean_Compiler_LCNF_Simp_simp(x_2699, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2698);
if (lean_obj_tag(x_2700) == 0)
{
lean_object* x_2701; lean_object* x_2702; lean_object* x_2703; lean_object* x_2704; lean_object* x_2705; 
x_2701 = lean_ctor_get(x_2700, 0);
lean_inc(x_2701);
x_2702 = lean_ctor_get(x_2700, 1);
lean_inc(x_2702);
if (lean_is_exclusive(x_2700)) {
 lean_ctor_release(x_2700, 0);
 lean_ctor_release(x_2700, 1);
 x_2703 = x_2700;
} else {
 lean_dec_ref(x_2700);
 x_2703 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2704 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2704 = x_22;
}
lean_ctor_set(x_2704, 0, x_2701);
if (lean_is_scalar(x_2703)) {
 x_2705 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2705 = x_2703;
}
lean_ctor_set(x_2705, 0, x_2704);
lean_ctor_set(x_2705, 1, x_2702);
return x_2705;
}
else
{
lean_object* x_2706; lean_object* x_2707; lean_object* x_2708; lean_object* x_2709; 
lean_dec(x_22);
x_2706 = lean_ctor_get(x_2700, 0);
lean_inc(x_2706);
x_2707 = lean_ctor_get(x_2700, 1);
lean_inc(x_2707);
if (lean_is_exclusive(x_2700)) {
 lean_ctor_release(x_2700, 0);
 lean_ctor_release(x_2700, 1);
 x_2708 = x_2700;
} else {
 lean_dec_ref(x_2700);
 x_2708 = lean_box(0);
}
if (lean_is_scalar(x_2708)) {
 x_2709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2709 = x_2708;
}
lean_ctor_set(x_2709, 0, x_2706);
lean_ctor_set(x_2709, 1, x_2707);
return x_2709;
}
}
}
else
{
uint8_t x_2710; 
lean_dec(x_2677);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2710 = !lean_is_exclusive(x_2680);
if (x_2710 == 0)
{
return x_2680;
}
else
{
lean_object* x_2711; lean_object* x_2712; lean_object* x_2713; 
x_2711 = lean_ctor_get(x_2680, 0);
x_2712 = lean_ctor_get(x_2680, 1);
lean_inc(x_2712);
lean_inc(x_2711);
lean_dec(x_2680);
x_2713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2713, 0, x_2711);
lean_ctor_set(x_2713, 1, x_2712);
return x_2713;
}
}
}
else
{
uint8_t x_2714; 
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
x_2714 = !lean_is_exclusive(x_2676);
if (x_2714 == 0)
{
return x_2676;
}
else
{
lean_object* x_2715; lean_object* x_2716; lean_object* x_2717; 
x_2715 = lean_ctor_get(x_2676, 0);
x_2716 = lean_ctor_get(x_2676, 1);
lean_inc(x_2716);
lean_inc(x_2715);
lean_dec(x_2676);
x_2717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2717, 0, x_2715);
lean_ctor_set(x_2717, 1, x_2716);
return x_2717;
}
}
}
}
}
}
else
{
uint8_t x_2718; 
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
x_2718 = !lean_is_exclusive(x_12);
if (x_2718 == 0)
{
return x_12;
}
else
{
lean_object* x_2719; lean_object* x_2720; lean_object* x_2721; 
x_2719 = lean_ctor_get(x_12, 0);
x_2720 = lean_ctor_get(x_12, 1);
lean_inc(x_2720);
lean_inc(x_2719);
lean_dec(x_12);
x_2721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2721, 0, x_2719);
lean_ctor_set(x_2721, 1, x_2720);
return x_2721;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_15);
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
lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
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
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_34, 1);
x_45 = lean_ctor_get(x_34, 0);
lean_dec(x_45);
lean_inc(x_4);
x_46 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; size_t x_49; size_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_50 = lean_ptr_addr(x_31);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_46, 0, x_34);
return x_46;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = lean_ptr_addr(x_2);
x_53 = lean_ptr_addr(x_4);
x_54 = lean_usize_dec_eq(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_46, 0, x_34);
return x_46;
}
else
{
lean_free_object(x_34);
lean_dec(x_31);
lean_dec(x_4);
lean_ctor_set(x_46, 0, x_3);
return x_46;
}
}
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_57 = lean_ptr_addr(x_31);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_3);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 0, x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
x_60 = lean_ptr_addr(x_2);
x_61 = lean_ptr_addr(x_4);
x_62 = lean_usize_dec_eq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_3);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 0, x_4);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_34);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
else
{
lean_object* x_64; 
lean_free_object(x_34);
lean_dec(x_31);
lean_dec(x_4);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_3);
lean_ctor_set(x_64, 1, x_55);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_34, 1);
lean_inc(x_65);
lean_dec(x_34);
lean_inc(x_4);
x_66 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_65);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_ptr_addr(x_1);
lean_dec(x_1);
x_70 = lean_ptr_addr(x_31);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_3);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_31);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
return x_73;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = lean_ptr_addr(x_2);
x_75 = lean_ptr_addr(x_4);
x_76 = lean_usize_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_31);
if (lean_is_scalar(x_68)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_68;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_67);
return x_78;
}
else
{
lean_object* x_79; 
lean_dec(x_31);
lean_dec(x_4);
if (lean_is_scalar(x_68)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_68;
}
lean_ctor_set(x_79, 0, x_3);
lean_ctor_set(x_79, 1, x_67);
return x_79;
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_30);
if (x_80 == 0)
{
return x_30;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_30, 0);
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_30);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_84 = lean_ctor_get(x_28, 0);
lean_inc(x_84);
lean_dec(x_28);
x_85 = lean_ctor_get(x_27, 1);
lean_inc(x_85);
lean_dec(x_27);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_4, 0);
lean_inc(x_88);
x_89 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_88, x_87, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_85);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_90);
lean_dec(x_4);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_86, x_94, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_95);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_86);
return x_96;
}
else
{
uint8_t x_97; 
lean_dec(x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
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
lean_dec(x_86);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
return x_89;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_27);
if (x_105 == 0)
{
return x_27;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_27, 0);
x_107 = lean_ctor_get(x_27, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_27);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_1);
x_109 = lean_ctor_get(x_24, 1);
lean_inc(x_109);
lean_dec(x_24);
x_110 = lean_ctor_get(x_25, 0);
lean_inc(x_110);
lean_dec(x_25);
x_111 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_109);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_dec(x_113);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
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
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_24);
if (x_116 == 0)
{
return x_24;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_24, 0);
x_118 = lean_ctor_get(x_24, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_24);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_20);
lean_dec(x_3);
x_120 = lean_ctor_get(x_21, 1);
lean_inc(x_120);
lean_dec(x_21);
x_121 = lean_ctor_get(x_22, 0);
lean_inc(x_121);
lean_dec(x_22);
x_122 = lean_ctor_get(x_4, 0);
lean_inc(x_122);
x_123 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_122, x_121, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_120);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_124);
lean_dec(x_4);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_126);
return x_127;
}
else
{
uint8_t x_128; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
return x_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 0);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_123);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_4);
lean_dec(x_3);
x_132 = lean_ctor_get(x_17, 1);
lean_inc(x_132);
lean_dec(x_17);
x_133 = lean_ctor_get(x_18, 0);
lean_inc(x_133);
lean_dec(x_18);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_1);
x_135 = l_Lean_Compiler_LCNF_Simp_simp(x_134, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_132);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_17);
if (x_136 == 0)
{
return x_17;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_17, 0);
x_138 = lean_ctor_get(x_17, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_17);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_4);
lean_dec(x_3);
x_140 = lean_ctor_get(x_14, 1);
lean_inc(x_140);
lean_dec(x_14);
x_141 = lean_ctor_get(x_15, 0);
lean_inc(x_141);
lean_dec(x_15);
x_142 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_140);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_144 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_141, x_145, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_146);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_141);
return x_147;
}
else
{
uint8_t x_148; 
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_144, 0);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_144);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_14);
if (x_152 == 0)
{
return x_14;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_14, 0);
x_154 = lean_ctor_get(x_14, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_14);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
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
lean_dec(x_5);
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
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
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
lean_dec(x_5);
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
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_dec(x_19);
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_13);
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
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
x_21 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_22 = lean_ctor_get(x_7, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
x_24 = lean_nat_dec_eq(x_13, x_14);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_26 = lean_ctor_get(x_7, 11);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 10);
lean_dec(x_27);
x_28 = lean_ctor_get(x_7, 9);
lean_dec(x_28);
x_29 = lean_ctor_get(x_7, 8);
lean_dec(x_29);
x_30 = lean_ctor_get(x_7, 7);
lean_dec(x_30);
x_31 = lean_ctor_get(x_7, 6);
lean_dec(x_31);
x_32 = lean_ctor_get(x_7, 5);
lean_dec(x_32);
x_33 = lean_ctor_get(x_7, 4);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_7, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_7, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_7, 0);
lean_dec(x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_13, x_38);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_39);
x_40 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = 0;
lean_inc(x_42);
x_45 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_44, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1754_(x_42, x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_43, x_42, x_1, x_46, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_51);
lean_dec(x_50);
lean_dec(x_42);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_43, x_42, x_1, x_46, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_42);
return x_54;
}
}
case 1:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_dec(x_40);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_55);
lean_dec(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
lean_inc(x_1);
lean_inc(x_56);
x_63 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed), 14, 4);
lean_closure_set(x_63, 0, x_57);
lean_closure_set(x_63, 1, x_56);
lean_closure_set(x_63, 2, x_1);
lean_closure_set(x_63, 3, x_60);
x_64 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_box(0);
x_66 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_63, x_56, x_65, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_56, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 2);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_67, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_63, x_56, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_72 = lean_st_ref_get(x_3, x_62);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = l_Lean_Compiler_LCNF_normFunDeclImp(x_76, x_56, x_75, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_80 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_78, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_63, x_81, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
lean_dec(x_84);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_80);
if (x_87 == 0)
{
return x_80;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_80, 0);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_80);
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
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_77);
if (x_91 == 0)
{
return x_77;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_77, 0);
x_93 = lean_ctor_get(x_77, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_77);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_59, 1);
lean_inc(x_95);
lean_dec(x_59);
x_96 = lean_st_ref_get(x_3, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_56);
x_101 = l_Lean_Compiler_LCNF_normFunDeclImp(x_100, x_56, x_99, x_5, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_box(0);
x_105 = lean_unbox(x_60);
lean_dec(x_60);
x_106 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_57, x_56, x_1, x_105, x_102, x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_103);
lean_dec(x_56);
return x_106;
}
else
{
uint8_t x_107; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_101);
if (x_107 == 0)
{
return x_101;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_101, 0);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_101);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
case 2:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_40, 1);
lean_inc(x_111);
lean_dec(x_40);
x_112 = lean_ctor_get(x_1, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_1, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
lean_dec(x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_1);
lean_inc(x_112);
x_119 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 14, 4);
lean_closure_set(x_119, 0, x_113);
lean_closure_set(x_119, 1, x_112);
lean_closure_set(x_119, 2, x_1);
lean_closure_set(x_119, 3, x_116);
x_120 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_box(0);
x_122 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_119, x_112, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_118);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_112, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 2);
lean_inc(x_124);
x_125 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_123, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_box(0);
x_127 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_119, x_112, x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_118);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_128 = lean_st_ref_get(x_3, x_118);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_133 = l_Lean_Compiler_LCNF_normFunDeclImp(x_132, x_112, x_131, x_5, x_6, x_7, x_8, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_134, x_5, x_6, x_7, x_8, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_119, x_137, x_140, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
lean_dec(x_140);
return x_142;
}
else
{
uint8_t x_143; 
lean_dec(x_119);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_136);
if (x_143 == 0)
{
return x_136;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_136, 0);
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_136);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_119);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
lean_dec(x_115);
x_152 = lean_st_ref_get(x_3, x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_112);
x_157 = l_Lean_Compiler_LCNF_normFunDeclImp(x_156, x_112, x_155, x_5, x_6, x_7, x_8, x_154);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_box(0);
x_161 = lean_unbox(x_116);
lean_dec(x_116);
x_162 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_113, x_112, x_1, x_161, x_158, x_160, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_159);
lean_dec(x_112);
return x_162;
}
else
{
uint8_t x_163; 
lean_dec(x_116);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_157);
if (x_163 == 0)
{
return x_157;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_157, 0);
x_165 = lean_ctor_get(x_157, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_157);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
case 3:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_167 = lean_ctor_get(x_40, 1);
lean_inc(x_167);
lean_dec(x_40);
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_1, 1);
lean_inc(x_169);
x_170 = lean_st_ref_get(x_3, x_167);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = 0;
lean_inc(x_168);
x_175 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_173, x_168, x_174);
lean_dec(x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_200; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec(x_175);
lean_inc(x_169);
x_177 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_174, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_172);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
lean_inc(x_178);
x_200 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_176, x_178, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_179);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_176);
x_203 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_176, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_202);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_array_get_size(x_178);
x_206 = lean_unsigned_to_nat(0u);
x_207 = lean_nat_dec_lt(x_206, x_205);
if (x_207 == 0)
{
lean_dec(x_205);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = x_204;
goto block_199;
}
else
{
uint8_t x_208; 
x_208 = lean_nat_dec_le(x_205, x_205);
if (x_208 == 0)
{
lean_dec(x_205);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = x_204;
goto block_199;
}
else
{
size_t x_209; size_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = 0;
x_210 = lean_usize_of_nat(x_205);
lean_dec(x_205);
x_211 = lean_box(0);
x_212 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_178, x_209, x_210, x_211, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_204);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_181 = x_213;
goto block_199;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_1);
x_214 = lean_ctor_get(x_200, 1);
lean_inc(x_214);
lean_dec(x_200);
x_215 = lean_ctor_get(x_201, 0);
lean_inc(x_215);
lean_dec(x_201);
x_1 = x_215;
x_9 = x_214;
goto _start;
}
}
else
{
uint8_t x_217; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_200);
if (x_217 == 0)
{
return x_200;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_200, 0);
x_219 = lean_ctor_get(x_200, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_200);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
block_199:
{
uint8_t x_182; 
x_182 = lean_name_eq(x_168, x_176);
lean_dec(x_168);
if (x_182 == 0)
{
uint8_t x_183; 
lean_dec(x_169);
x_183 = !lean_is_exclusive(x_1);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_1, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_1, 0);
lean_dec(x_185);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_176);
if (lean_is_scalar(x_180)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_180;
}
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_181);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_1);
x_187 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_187, 0, x_176);
lean_ctor_set(x_187, 1, x_178);
if (lean_is_scalar(x_180)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_180;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_181);
return x_188;
}
}
else
{
size_t x_189; size_t x_190; uint8_t x_191; 
x_189 = lean_ptr_addr(x_169);
lean_dec(x_169);
x_190 = lean_ptr_addr(x_178);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_1);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_1, 1);
lean_dec(x_193);
x_194 = lean_ctor_get(x_1, 0);
lean_dec(x_194);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_176);
if (lean_is_scalar(x_180)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_180;
}
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_181);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_1);
x_196 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_196, 0, x_176);
lean_ctor_set(x_196, 1, x_178);
if (lean_is_scalar(x_180)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_180;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_181);
return x_197;
}
}
else
{
lean_object* x_198; 
lean_dec(x_178);
lean_dec(x_176);
if (lean_is_scalar(x_180)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_180;
}
lean_ctor_set(x_198, 0, x_1);
lean_ctor_set(x_198, 1, x_181);
return x_198;
}
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_172);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_221;
}
}
case 4:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_40, 1);
lean_inc(x_222);
lean_dec(x_40);
x_223 = lean_ctor_get(x_1, 0);
lean_inc(x_223);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_223);
x_224 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; 
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_223, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 x_231 = x_223;
} else {
 lean_dec_ref(x_223);
 x_231 = lean_box(0);
}
x_232 = lean_st_ref_get(x_3, x_226);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec(x_233);
x_236 = 0;
lean_inc(x_229);
x_237 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_235, x_229, x_236);
lean_dec(x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
x_239 = lean_st_ref_get(x_3, x_234);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
lean_inc(x_228);
x_243 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_242, x_236, x_228);
lean_dec(x_242);
lean_inc(x_238);
x_244 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_238, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_241);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
lean_inc(x_238);
x_246 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 10, 1);
lean_closure_set(x_246, 0, x_238);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_230);
x_247 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_230, x_246, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
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
x_251 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_248, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_286; lean_object* x_298; uint8_t x_299; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_298 = lean_array_get_size(x_252);
x_299 = lean_nat_dec_eq(x_298, x_38);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_298);
lean_dec(x_250);
x_300 = lean_box(0);
x_255 = x_300;
goto block_285;
}
else
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_unsigned_to_nat(0u);
x_302 = lean_nat_dec_lt(x_301, x_298);
lean_dec(x_298);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_304 = l_outOfBounds___rarg(x_303);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
lean_dec(x_304);
lean_dec(x_250);
x_305 = lean_box(0);
x_255 = x_305;
goto block_285;
}
else
{
lean_object* x_306; 
lean_dec(x_304);
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_1);
x_306 = lean_box(0);
x_286 = x_306;
goto block_297;
}
}
else
{
lean_object* x_307; 
x_307 = lean_array_fget(x_252, x_301);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
lean_dec(x_307);
lean_dec(x_250);
x_308 = lean_box(0);
x_255 = x_308;
goto block_285;
}
else
{
lean_object* x_309; 
lean_dec(x_307);
lean_dec(x_254);
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_1);
x_309 = lean_box(0);
x_286 = x_309;
goto block_297;
}
}
}
block_285:
{
size_t x_256; size_t x_257; uint8_t x_258; 
lean_dec(x_255);
x_256 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_257 = lean_ptr_addr(x_252);
x_258 = lean_usize_dec_eq(x_256, x_257);
if (x_258 == 0)
{
uint8_t x_259; 
lean_dec(x_229);
lean_dec(x_228);
x_259 = !lean_is_exclusive(x_1);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_1, 0);
lean_dec(x_260);
if (lean_is_scalar(x_231)) {
 x_261 = lean_alloc_ctor(0, 4, 0);
} else {
 x_261 = x_231;
}
lean_ctor_set(x_261, 0, x_227);
lean_ctor_set(x_261, 1, x_243);
lean_ctor_set(x_261, 2, x_238);
lean_ctor_set(x_261, 3, x_252);
lean_ctor_set(x_1, 0, x_261);
if (lean_is_scalar(x_254)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_254;
}
lean_ctor_set(x_262, 0, x_1);
lean_ctor_set(x_262, 1, x_253);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_1);
if (lean_is_scalar(x_231)) {
 x_263 = lean_alloc_ctor(0, 4, 0);
} else {
 x_263 = x_231;
}
lean_ctor_set(x_263, 0, x_227);
lean_ctor_set(x_263, 1, x_243);
lean_ctor_set(x_263, 2, x_238);
lean_ctor_set(x_263, 3, x_252);
x_264 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_264, 0, x_263);
if (lean_is_scalar(x_254)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_254;
}
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_253);
return x_265;
}
}
else
{
size_t x_266; size_t x_267; uint8_t x_268; 
x_266 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_267 = lean_ptr_addr(x_243);
x_268 = lean_usize_dec_eq(x_266, x_267);
if (x_268 == 0)
{
uint8_t x_269; 
lean_dec(x_229);
x_269 = !lean_is_exclusive(x_1);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_1, 0);
lean_dec(x_270);
if (lean_is_scalar(x_231)) {
 x_271 = lean_alloc_ctor(0, 4, 0);
} else {
 x_271 = x_231;
}
lean_ctor_set(x_271, 0, x_227);
lean_ctor_set(x_271, 1, x_243);
lean_ctor_set(x_271, 2, x_238);
lean_ctor_set(x_271, 3, x_252);
lean_ctor_set(x_1, 0, x_271);
if (lean_is_scalar(x_254)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_254;
}
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_253);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_1);
if (lean_is_scalar(x_231)) {
 x_273 = lean_alloc_ctor(0, 4, 0);
} else {
 x_273 = x_231;
}
lean_ctor_set(x_273, 0, x_227);
lean_ctor_set(x_273, 1, x_243);
lean_ctor_set(x_273, 2, x_238);
lean_ctor_set(x_273, 3, x_252);
x_274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_274, 0, x_273);
if (lean_is_scalar(x_254)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_254;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_253);
return x_275;
}
}
else
{
uint8_t x_276; 
x_276 = lean_name_eq(x_229, x_238);
lean_dec(x_229);
if (x_276 == 0)
{
uint8_t x_277; 
x_277 = !lean_is_exclusive(x_1);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_1, 0);
lean_dec(x_278);
if (lean_is_scalar(x_231)) {
 x_279 = lean_alloc_ctor(0, 4, 0);
} else {
 x_279 = x_231;
}
lean_ctor_set(x_279, 0, x_227);
lean_ctor_set(x_279, 1, x_243);
lean_ctor_set(x_279, 2, x_238);
lean_ctor_set(x_279, 3, x_252);
lean_ctor_set(x_1, 0, x_279);
if (lean_is_scalar(x_254)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_254;
}
lean_ctor_set(x_280, 0, x_1);
lean_ctor_set(x_280, 1, x_253);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_1);
if (lean_is_scalar(x_231)) {
 x_281 = lean_alloc_ctor(0, 4, 0);
} else {
 x_281 = x_231;
}
lean_ctor_set(x_281, 0, x_227);
lean_ctor_set(x_281, 1, x_243);
lean_ctor_set(x_281, 2, x_238);
lean_ctor_set(x_281, 3, x_252);
x_282 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_282, 0, x_281);
if (lean_is_scalar(x_254)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_254;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_253);
return x_283;
}
}
else
{
lean_object* x_284; 
lean_dec(x_252);
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_227);
if (lean_is_scalar(x_254)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_254;
}
lean_ctor_set(x_284, 0, x_1);
lean_ctor_set(x_284, 1, x_253);
return x_284;
}
}
}
}
block_297:
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_286);
x_287 = lean_array_get_size(x_252);
x_288 = lean_unsigned_to_nat(0u);
x_289 = lean_nat_dec_lt(x_288, x_287);
lean_dec(x_287);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_252);
x_290 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_291 = l_outOfBounds___rarg(x_290);
x_292 = l_Lean_Compiler_LCNF_AltCore_getCode(x_291);
lean_dec(x_291);
if (lean_is_scalar(x_250)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_250;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_253);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_array_fget(x_252, x_288);
lean_dec(x_252);
x_295 = l_Lean_Compiler_LCNF_AltCore_getCode(x_294);
lean_dec(x_294);
if (lean_is_scalar(x_250)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_250;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_253);
return x_296;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_251);
if (x_310 == 0)
{
return x_251;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_251, 0);
x_312 = lean_ctor_get(x_251, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_251);
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
lean_dec(x_243);
lean_dec(x_238);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_247);
if (x_314 == 0)
{
return x_247;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_247, 0);
x_316 = lean_ctor_get(x_247, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_247);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_318 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_234);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_318;
}
}
else
{
uint8_t x_319; 
lean_dec(x_223);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_319 = !lean_is_exclusive(x_224);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_224, 0);
lean_dec(x_320);
x_321 = lean_ctor_get(x_225, 0);
lean_inc(x_321);
lean_dec(x_225);
lean_ctor_set(x_224, 0, x_321);
return x_224;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_224, 1);
lean_inc(x_322);
lean_dec(x_224);
x_323 = lean_ctor_get(x_225, 0);
lean_inc(x_323);
lean_dec(x_225);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_223);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_224);
if (x_325 == 0)
{
return x_224;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_224, 0);
x_327 = lean_ctor_get(x_224, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_224);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
case 5:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; 
x_329 = lean_ctor_get(x_40, 1);
lean_inc(x_329);
lean_dec(x_40);
x_330 = lean_ctor_get(x_1, 0);
lean_inc(x_330);
x_331 = lean_st_ref_get(x_3, x_329);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
lean_dec(x_332);
x_335 = 0;
lean_inc(x_330);
x_336 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_334, x_330, x_335);
lean_dec(x_334);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec(x_336);
lean_inc(x_337);
x_338 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_ctor_get(x_338, 0);
lean_dec(x_340);
x_341 = lean_name_eq(x_330, x_337);
lean_dec(x_330);
if (x_341 == 0)
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_1);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_1, 0);
lean_dec(x_343);
lean_ctor_set(x_1, 0, x_337);
lean_ctor_set(x_338, 0, x_1);
return x_338;
}
else
{
lean_object* x_344; 
lean_dec(x_1);
x_344 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_344, 0, x_337);
lean_ctor_set(x_338, 0, x_344);
return x_338;
}
}
else
{
lean_dec(x_337);
lean_ctor_set(x_338, 0, x_1);
return x_338;
}
}
else
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
lean_dec(x_338);
x_346 = lean_name_eq(x_330, x_337);
lean_dec(x_330);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_347 = x_1;
} else {
 lean_dec_ref(x_1);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(5, 1, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_337);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_345);
return x_349;
}
else
{
lean_object* x_350; 
lean_dec(x_337);
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_1);
lean_ctor_set(x_350, 1, x_345);
return x_350;
}
}
}
else
{
lean_object* x_351; 
lean_dec(x_330);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_351;
}
}
default: 
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; 
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_352 = lean_ctor_get(x_40, 1);
lean_inc(x_352);
lean_dec(x_40);
x_353 = lean_ctor_get(x_1, 0);
lean_inc(x_353);
x_354 = lean_st_ref_get(x_3, x_352);
lean_dec(x_3);
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; size_t x_360; size_t x_361; uint8_t x_362; 
x_356 = lean_ctor_get(x_354, 0);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
lean_dec(x_356);
x_358 = 0;
lean_inc(x_353);
x_359 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_357, x_358, x_353);
lean_dec(x_357);
x_360 = lean_ptr_addr(x_353);
lean_dec(x_353);
x_361 = lean_ptr_addr(x_359);
x_362 = lean_usize_dec_eq(x_360, x_361);
if (x_362 == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_1);
if (x_363 == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_1, 0);
lean_dec(x_364);
lean_ctor_set(x_1, 0, x_359);
lean_ctor_set(x_354, 0, x_1);
return x_354;
}
else
{
lean_object* x_365; 
lean_dec(x_1);
x_365 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_365, 0, x_359);
lean_ctor_set(x_354, 0, x_365);
return x_354;
}
}
else
{
lean_dec(x_359);
lean_ctor_set(x_354, 0, x_1);
return x_354;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; size_t x_371; size_t x_372; uint8_t x_373; 
x_366 = lean_ctor_get(x_354, 0);
x_367 = lean_ctor_get(x_354, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_354);
x_368 = lean_ctor_get(x_366, 0);
lean_inc(x_368);
lean_dec(x_366);
x_369 = 0;
lean_inc(x_353);
x_370 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_368, x_369, x_353);
lean_dec(x_368);
x_371 = lean_ptr_addr(x_353);
lean_dec(x_353);
x_372 = lean_ptr_addr(x_370);
x_373 = lean_usize_dec_eq(x_371, x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_374 = x_1;
} else {
 lean_dec_ref(x_1);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(6, 1, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_370);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_367);
return x_376;
}
else
{
lean_object* x_377; 
lean_dec(x_370);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_1);
lean_ctor_set(x_377, 1, x_367);
return x_377;
}
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_7);
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_nat_add(x_13, x_378);
lean_dec(x_13);
x_380 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_380, 0, x_10);
lean_ctor_set(x_380, 1, x_11);
lean_ctor_set(x_380, 2, x_12);
lean_ctor_set(x_380, 3, x_379);
lean_ctor_set(x_380, 4, x_14);
lean_ctor_set(x_380, 5, x_15);
lean_ctor_set(x_380, 6, x_16);
lean_ctor_set(x_380, 7, x_17);
lean_ctor_set(x_380, 8, x_18);
lean_ctor_set(x_380, 9, x_19);
lean_ctor_set(x_380, 10, x_20);
lean_ctor_set(x_380, 11, x_22);
lean_ctor_set_uint8(x_380, sizeof(void*)*12, x_21);
lean_ctor_set_uint8(x_380, sizeof(void*)*12 + 1, x_23);
x_381 = l_Lean_Compiler_LCNF_Simp_incVisited___rarg(x_3, x_4, x_5, x_6, x_380, x_8, x_9);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
lean_dec(x_381);
x_383 = lean_ctor_get(x_1, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_1, 1);
lean_inc(x_384);
x_385 = 0;
lean_inc(x_383);
x_386 = l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(x_385, x_383, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_382);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1754_(x_383, x_387);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_390 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_380, x_8, x_388);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_384, x_383, x_1, x_387, x_391, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_392);
lean_dec(x_391);
lean_dec(x_383);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_box(0);
x_395 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_384, x_383, x_1, x_387, x_394, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_388);
lean_dec(x_383);
return x_395;
}
}
case 1:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_396 = lean_ctor_get(x_381, 1);
lean_inc(x_396);
lean_dec(x_381);
x_397 = lean_ctor_get(x_1, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_1, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
x_400 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_399, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_396);
lean_dec(x_399);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_unbox(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_403 = lean_ctor_get(x_400, 1);
lean_inc(x_403);
lean_dec(x_400);
lean_inc(x_1);
lean_inc(x_397);
x_404 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed), 14, 4);
lean_closure_set(x_404, 0, x_398);
lean_closure_set(x_404, 1, x_397);
lean_closure_set(x_404, 2, x_1);
lean_closure_set(x_404, 3, x_401);
x_405 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_box(0);
x_407 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_404, x_397, x_406, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_403);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; uint8_t x_410; 
x_408 = lean_ctor_get(x_397, 3);
lean_inc(x_408);
x_409 = lean_ctor_get(x_397, 2);
lean_inc(x_409);
x_410 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_408, x_409);
lean_dec(x_409);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_box(0);
x_412 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_404, x_397, x_411, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_403);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; 
x_413 = lean_st_ref_get(x_3, x_403);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
lean_dec(x_413);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec(x_414);
x_417 = 0;
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
x_418 = l_Lean_Compiler_LCNF_normFunDeclImp(x_417, x_397, x_416, x_5, x_6, x_380, x_8, x_415);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_418, 1);
lean_inc(x_420);
lean_dec(x_418);
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
x_421 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_419, x_5, x_6, x_380, x_8, x_420);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_421, 1);
lean_inc(x_423);
lean_dec(x_421);
x_424 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_380, x_8, x_423);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_404, x_422, x_425, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_426);
lean_dec(x_425);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_404);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_428 = lean_ctor_get(x_421, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_421, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_430 = x_421;
} else {
 lean_dec_ref(x_421);
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
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_404);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_432 = lean_ctor_get(x_418, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_418, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_434 = x_418;
} else {
 lean_dec_ref(x_418);
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
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; 
x_436 = lean_ctor_get(x_400, 1);
lean_inc(x_436);
lean_dec(x_400);
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
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_397);
x_442 = l_Lean_Compiler_LCNF_normFunDeclImp(x_441, x_397, x_440, x_5, x_6, x_380, x_8, x_439);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_box(0);
x_446 = lean_unbox(x_401);
lean_dec(x_401);
x_447 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_398, x_397, x_1, x_446, x_443, x_445, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_444);
lean_dec(x_397);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_401);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_448 = lean_ctor_get(x_442, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_442, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_450 = x_442;
} else {
 lean_dec_ref(x_442);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
}
case 2:
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_452 = lean_ctor_get(x_381, 1);
lean_inc(x_452);
lean_dec(x_381);
x_453 = lean_ctor_get(x_1, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_1, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
x_456 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(x_455, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_452);
lean_dec(x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_unbox(x_457);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
lean_inc(x_1);
lean_inc(x_453);
x_460 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed), 14, 4);
lean_closure_set(x_460, 0, x_454);
lean_closure_set(x_460, 1, x_453);
lean_closure_set(x_460, 2, x_1);
lean_closure_set(x_460, 3, x_457);
x_461 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_box(0);
x_463 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_460, x_453, x_462, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_459);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_464 = lean_ctor_get(x_453, 3);
lean_inc(x_464);
x_465 = lean_ctor_get(x_453, 2);
lean_inc(x_465);
x_466 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_464, x_465);
lean_dec(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_box(0);
x_468 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_460, x_453, x_467, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_459);
return x_468;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; 
x_469 = lean_st_ref_get(x_3, x_459);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec(x_470);
x_473 = 0;
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
x_474 = l_Lean_Compiler_LCNF_normFunDeclImp(x_473, x_453, x_472, x_5, x_6, x_380, x_8, x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
x_477 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_475, x_5, x_6, x_380, x_8, x_476);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
x_480 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_380, x_8, x_479);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_460, x_478, x_481, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_482);
lean_dec(x_481);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_460);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_484 = lean_ctor_get(x_477, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_477, 1);
lean_inc(x_485);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_486 = x_477;
} else {
 lean_dec_ref(x_477);
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
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_460);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_488 = lean_ctor_get(x_474, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_474, 1);
lean_inc(x_489);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_490 = x_474;
} else {
 lean_dec_ref(x_474);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_489);
return x_491;
}
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; lean_object* x_498; 
x_492 = lean_ctor_get(x_456, 1);
lean_inc(x_492);
lean_dec(x_456);
x_493 = lean_st_ref_get(x_3, x_492);
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
lean_dec(x_494);
x_497 = 0;
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_453);
x_498 = l_Lean_Compiler_LCNF_normFunDeclImp(x_497, x_453, x_496, x_5, x_6, x_380, x_8, x_495);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; uint8_t x_502; lean_object* x_503; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_box(0);
x_502 = lean_unbox(x_457);
lean_dec(x_457);
x_503 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_454, x_453, x_1, x_502, x_499, x_501, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_500);
lean_dec(x_453);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_453);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_498, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_498, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_506 = x_498;
} else {
 lean_dec_ref(x_498);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
}
case 3:
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_508 = lean_ctor_get(x_381, 1);
lean_inc(x_508);
lean_dec(x_381);
x_509 = lean_ctor_get(x_1, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_1, 1);
lean_inc(x_510);
x_511 = lean_st_ref_get(x_3, x_508);
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_ctor_get(x_512, 0);
lean_inc(x_514);
lean_dec(x_512);
x_515 = 0;
lean_inc(x_509);
x_516 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_514, x_509, x_515);
lean_dec(x_514);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_535; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
lean_dec(x_516);
lean_inc(x_510);
x_518 = l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(x_515, x_510, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_513);
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_521 = x_518;
} else {
 lean_dec_ref(x_518);
 x_521 = lean_box(0);
}
lean_inc(x_519);
x_535 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_517, x_519, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_520);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
lean_inc(x_517);
x_538 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_517, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_537);
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
lean_dec(x_538);
x_540 = lean_array_get_size(x_519);
x_541 = lean_unsigned_to_nat(0u);
x_542 = lean_nat_dec_lt(x_541, x_540);
if (x_542 == 0)
{
lean_dec(x_540);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_522 = x_539;
goto block_534;
}
else
{
uint8_t x_543; 
x_543 = lean_nat_dec_le(x_540, x_540);
if (x_543 == 0)
{
lean_dec(x_540);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_522 = x_539;
goto block_534;
}
else
{
size_t x_544; size_t x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_544 = 0;
x_545 = lean_usize_of_nat(x_540);
lean_dec(x_540);
x_546 = lean_box(0);
x_547 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_LCNF_Simp_markUsedLetValue___spec__1(x_519, x_544, x_545, x_546, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_539);
lean_dec(x_8);
lean_dec(x_380);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_522 = x_548;
goto block_534;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_1);
x_549 = lean_ctor_get(x_535, 1);
lean_inc(x_549);
lean_dec(x_535);
x_550 = lean_ctor_get(x_536, 0);
lean_inc(x_550);
lean_dec(x_536);
x_1 = x_550;
x_7 = x_380;
x_9 = x_549;
goto _start;
}
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_521);
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_552 = lean_ctor_get(x_535, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_535, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_554 = x_535;
} else {
 lean_dec_ref(x_535);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
block_534:
{
uint8_t x_523; 
x_523 = lean_name_eq(x_509, x_517);
lean_dec(x_509);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
lean_dec(x_510);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_524 = x_1;
} else {
 lean_dec_ref(x_1);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_524)) {
 x_525 = lean_alloc_ctor(3, 2, 0);
} else {
 x_525 = x_524;
}
lean_ctor_set(x_525, 0, x_517);
lean_ctor_set(x_525, 1, x_519);
if (lean_is_scalar(x_521)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_521;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_522);
return x_526;
}
else
{
size_t x_527; size_t x_528; uint8_t x_529; 
x_527 = lean_ptr_addr(x_510);
lean_dec(x_510);
x_528 = lean_ptr_addr(x_519);
x_529 = lean_usize_dec_eq(x_527, x_528);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_530 = x_1;
} else {
 lean_dec_ref(x_1);
 x_530 = lean_box(0);
}
if (lean_is_scalar(x_530)) {
 x_531 = lean_alloc_ctor(3, 2, 0);
} else {
 x_531 = x_530;
}
lean_ctor_set(x_531, 0, x_517);
lean_ctor_set(x_531, 1, x_519);
if (lean_is_scalar(x_521)) {
 x_532 = lean_alloc_ctor(0, 2, 0);
} else {
 x_532 = x_521;
}
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_522);
return x_532;
}
else
{
lean_object* x_533; 
lean_dec(x_519);
lean_dec(x_517);
if (lean_is_scalar(x_521)) {
 x_533 = lean_alloc_ctor(0, 2, 0);
} else {
 x_533 = x_521;
}
lean_ctor_set(x_533, 0, x_1);
lean_ctor_set(x_533, 1, x_522);
return x_533;
}
}
}
}
else
{
lean_object* x_556; 
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_556 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_380, x_8, x_513);
lean_dec(x_8);
lean_dec(x_380);
lean_dec(x_6);
lean_dec(x_5);
return x_556;
}
}
case 4:
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_381, 1);
lean_inc(x_557);
lean_dec(x_381);
x_558 = lean_ctor_get(x_1, 0);
lean_inc(x_558);
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_558);
x_559 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_558, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_557);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; 
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_558, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_558, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_558, 2);
lean_inc(x_564);
x_565 = lean_ctor_get(x_558, 3);
lean_inc(x_565);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 lean_ctor_release(x_558, 2);
 lean_ctor_release(x_558, 3);
 x_566 = x_558;
} else {
 lean_dec_ref(x_558);
 x_566 = lean_box(0);
}
x_567 = lean_st_ref_get(x_3, x_561);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
x_570 = lean_ctor_get(x_568, 0);
lean_inc(x_570);
lean_dec(x_568);
x_571 = 0;
lean_inc(x_564);
x_572 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_570, x_564, x_571);
lean_dec(x_570);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
lean_dec(x_572);
x_574 = lean_st_ref_get(x_3, x_569);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc(x_577);
lean_dec(x_575);
lean_inc(x_563);
x_578 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_577, x_571, x_563);
lean_dec(x_577);
lean_inc(x_573);
x_579 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_573, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_576);
x_580 = lean_ctor_get(x_579, 1);
lean_inc(x_580);
lean_dec(x_579);
lean_inc(x_573);
x_581 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lambda__8), 10, 1);
lean_closure_set(x_581, 0, x_573);
lean_inc(x_8);
lean_inc(x_380);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_565);
x_582 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(x_565, x_581, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_580);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
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
x_586 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_583, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_584);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_612; lean_object* x_624; uint8_t x_625; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_589 = x_586;
} else {
 lean_dec_ref(x_586);
 x_589 = lean_box(0);
}
x_624 = lean_array_get_size(x_587);
x_625 = lean_nat_dec_eq(x_624, x_378);
if (x_625 == 0)
{
lean_object* x_626; 
lean_dec(x_624);
lean_dec(x_585);
x_626 = lean_box(0);
x_590 = x_626;
goto block_611;
}
else
{
lean_object* x_627; uint8_t x_628; 
x_627 = lean_unsigned_to_nat(0u);
x_628 = lean_nat_dec_lt(x_627, x_624);
lean_dec(x_624);
if (x_628 == 0)
{
lean_object* x_629; lean_object* x_630; 
x_629 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_630 = l_outOfBounds___rarg(x_629);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; 
lean_dec(x_630);
lean_dec(x_585);
x_631 = lean_box(0);
x_590 = x_631;
goto block_611;
}
else
{
lean_object* x_632; 
lean_dec(x_630);
lean_dec(x_589);
lean_dec(x_578);
lean_dec(x_573);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_1);
x_632 = lean_box(0);
x_612 = x_632;
goto block_623;
}
}
else
{
lean_object* x_633; 
x_633 = lean_array_fget(x_587, x_627);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; 
lean_dec(x_633);
lean_dec(x_585);
x_634 = lean_box(0);
x_590 = x_634;
goto block_611;
}
else
{
lean_object* x_635; 
lean_dec(x_633);
lean_dec(x_589);
lean_dec(x_578);
lean_dec(x_573);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_1);
x_635 = lean_box(0);
x_612 = x_635;
goto block_623;
}
}
}
block_611:
{
size_t x_591; size_t x_592; uint8_t x_593; 
lean_dec(x_590);
x_591 = lean_ptr_addr(x_565);
lean_dec(x_565);
x_592 = lean_ptr_addr(x_587);
x_593 = lean_usize_dec_eq(x_591, x_592);
if (x_593 == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_564);
lean_dec(x_563);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_594 = x_1;
} else {
 lean_dec_ref(x_1);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_595 = lean_alloc_ctor(0, 4, 0);
} else {
 x_595 = x_566;
}
lean_ctor_set(x_595, 0, x_562);
lean_ctor_set(x_595, 1, x_578);
lean_ctor_set(x_595, 2, x_573);
lean_ctor_set(x_595, 3, x_587);
if (lean_is_scalar(x_594)) {
 x_596 = lean_alloc_ctor(4, 1, 0);
} else {
 x_596 = x_594;
}
lean_ctor_set(x_596, 0, x_595);
if (lean_is_scalar(x_589)) {
 x_597 = lean_alloc_ctor(0, 2, 0);
} else {
 x_597 = x_589;
}
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_597, 1, x_588);
return x_597;
}
else
{
size_t x_598; size_t x_599; uint8_t x_600; 
x_598 = lean_ptr_addr(x_563);
lean_dec(x_563);
x_599 = lean_ptr_addr(x_578);
x_600 = lean_usize_dec_eq(x_598, x_599);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_564);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_601 = x_1;
} else {
 lean_dec_ref(x_1);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_602 = lean_alloc_ctor(0, 4, 0);
} else {
 x_602 = x_566;
}
lean_ctor_set(x_602, 0, x_562);
lean_ctor_set(x_602, 1, x_578);
lean_ctor_set(x_602, 2, x_573);
lean_ctor_set(x_602, 3, x_587);
if (lean_is_scalar(x_601)) {
 x_603 = lean_alloc_ctor(4, 1, 0);
} else {
 x_603 = x_601;
}
lean_ctor_set(x_603, 0, x_602);
if (lean_is_scalar(x_589)) {
 x_604 = lean_alloc_ctor(0, 2, 0);
} else {
 x_604 = x_589;
}
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_588);
return x_604;
}
else
{
uint8_t x_605; 
x_605 = lean_name_eq(x_564, x_573);
lean_dec(x_564);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_606 = x_1;
} else {
 lean_dec_ref(x_1);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_607 = lean_alloc_ctor(0, 4, 0);
} else {
 x_607 = x_566;
}
lean_ctor_set(x_607, 0, x_562);
lean_ctor_set(x_607, 1, x_578);
lean_ctor_set(x_607, 2, x_573);
lean_ctor_set(x_607, 3, x_587);
if (lean_is_scalar(x_606)) {
 x_608 = lean_alloc_ctor(4, 1, 0);
} else {
 x_608 = x_606;
}
lean_ctor_set(x_608, 0, x_607);
if (lean_is_scalar(x_589)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_589;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_588);
return x_609;
}
else
{
lean_object* x_610; 
lean_dec(x_587);
lean_dec(x_578);
lean_dec(x_573);
lean_dec(x_566);
lean_dec(x_562);
if (lean_is_scalar(x_589)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_589;
}
lean_ctor_set(x_610, 0, x_1);
lean_ctor_set(x_610, 1, x_588);
return x_610;
}
}
}
}
block_623:
{
lean_object* x_613; lean_object* x_614; uint8_t x_615; 
lean_dec(x_612);
x_613 = lean_array_get_size(x_587);
x_614 = lean_unsigned_to_nat(0u);
x_615 = lean_nat_dec_lt(x_614, x_613);
lean_dec(x_613);
if (x_615 == 0)
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_587);
x_616 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
x_617 = l_outOfBounds___rarg(x_616);
x_618 = l_Lean_Compiler_LCNF_AltCore_getCode(x_617);
lean_dec(x_617);
if (lean_is_scalar(x_585)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_585;
}
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_588);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_array_fget(x_587, x_614);
lean_dec(x_587);
x_621 = l_Lean_Compiler_LCNF_AltCore_getCode(x_620);
lean_dec(x_620);
if (lean_is_scalar(x_585)) {
 x_622 = lean_alloc_ctor(0, 2, 0);
} else {
 x_622 = x_585;
}
lean_ctor_set(x_622, 0, x_621);
lean_ctor_set(x_622, 1, x_588);
return x_622;
}
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_585);
lean_dec(x_578);
lean_dec(x_573);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_1);
x_636 = lean_ctor_get(x_586, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_586, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_638 = x_586;
} else {
 lean_dec_ref(x_586);
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
lean_dec(x_578);
lean_dec(x_573);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_582, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_582, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_642 = x_582;
} else {
 lean_dec_ref(x_582);
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
else
{
lean_object* x_644; 
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_562);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_644 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_380, x_8, x_569);
lean_dec(x_8);
lean_dec(x_380);
lean_dec(x_6);
lean_dec(x_5);
return x_644;
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_558);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_645 = lean_ctor_get(x_559, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_646 = x_559;
} else {
 lean_dec_ref(x_559);
 x_646 = lean_box(0);
}
x_647 = lean_ctor_get(x_560, 0);
lean_inc(x_647);
lean_dec(x_560);
if (lean_is_scalar(x_646)) {
 x_648 = lean_alloc_ctor(0, 2, 0);
} else {
 x_648 = x_646;
}
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_645);
return x_648;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_558);
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_649 = lean_ctor_get(x_559, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_559, 1);
lean_inc(x_650);
if (lean_is_exclusive(x_559)) {
 lean_ctor_release(x_559, 0);
 lean_ctor_release(x_559, 1);
 x_651 = x_559;
} else {
 lean_dec_ref(x_559);
 x_651 = lean_box(0);
}
if (lean_is_scalar(x_651)) {
 x_652 = lean_alloc_ctor(1, 2, 0);
} else {
 x_652 = x_651;
}
lean_ctor_set(x_652, 0, x_649);
lean_ctor_set(x_652, 1, x_650);
return x_652;
}
}
case 5:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; uint8_t x_659; lean_object* x_660; 
x_653 = lean_ctor_get(x_381, 1);
lean_inc(x_653);
lean_dec(x_381);
x_654 = lean_ctor_get(x_1, 0);
lean_inc(x_654);
x_655 = lean_st_ref_get(x_3, x_653);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = lean_ctor_get(x_656, 0);
lean_inc(x_658);
lean_dec(x_656);
x_659 = 0;
lean_inc(x_654);
x_660 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_658, x_654, x_659);
lean_dec(x_658);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
lean_dec(x_660);
lean_inc(x_661);
x_662 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_661, x_2, x_3, x_4, x_5, x_6, x_380, x_8, x_657);
lean_dec(x_8);
lean_dec(x_380);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_664 = x_662;
} else {
 lean_dec_ref(x_662);
 x_664 = lean_box(0);
}
x_665 = lean_name_eq(x_654, x_661);
lean_dec(x_654);
if (x_665 == 0)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_666 = x_1;
} else {
 lean_dec_ref(x_1);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(5, 1, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_661);
if (lean_is_scalar(x_664)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_664;
}
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_663);
return x_668;
}
else
{
lean_object* x_669; 
lean_dec(x_661);
if (lean_is_scalar(x_664)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_664;
}
lean_ctor_set(x_669, 0, x_1);
lean_ctor_set(x_669, 1, x_663);
return x_669;
}
}
else
{
lean_object* x_670; 
lean_dec(x_654);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_670 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_380, x_8, x_657);
lean_dec(x_8);
lean_dec(x_380);
lean_dec(x_6);
lean_dec(x_5);
return x_670;
}
}
default: 
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; lean_object* x_679; size_t x_680; size_t x_681; uint8_t x_682; 
lean_dec(x_380);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_671 = lean_ctor_get(x_381, 1);
lean_inc(x_671);
lean_dec(x_381);
x_672 = lean_ctor_get(x_1, 0);
lean_inc(x_672);
x_673 = lean_st_ref_get(x_3, x_671);
lean_dec(x_3);
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_676 = x_673;
} else {
 lean_dec_ref(x_673);
 x_676 = lean_box(0);
}
x_677 = lean_ctor_get(x_674, 0);
lean_inc(x_677);
lean_dec(x_674);
x_678 = 0;
lean_inc(x_672);
x_679 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_677, x_678, x_672);
lean_dec(x_677);
x_680 = lean_ptr_addr(x_672);
lean_dec(x_672);
x_681 = lean_ptr_addr(x_679);
x_682 = lean_usize_dec_eq(x_680, x_681);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_683 = x_1;
} else {
 lean_dec_ref(x_1);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(6, 1, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_679);
if (lean_is_scalar(x_676)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_676;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_675);
return x_685;
}
else
{
lean_object* x_686; 
lean_dec(x_679);
if (lean_is_scalar(x_676)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_676;
}
lean_ctor_set(x_686, 0, x_1);
lean_ctor_set(x_686, 1, x_675);
return x_686;
}
}
}
}
}
else
{
lean_object* x_687; 
lean_dec(x_22);
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
x_687 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_687;
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(x_18, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_free_object(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_29);
x_31 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_ctor_set_tag(x_16, 4);
lean_ctor_set(x_16, 0, x_33);
x_34 = l_Lean_Compiler_LCNF_eraseCode(x_16, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_16);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_32) == 0)
{
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 2);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
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
lean_ctor_set(x_20, 0, x_51);
lean_ctor_set(x_53, 0, x_20);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_20, 0, x_51);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_38);
lean_free_object(x_20);
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
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_36);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_36, 1);
x_64 = lean_ctor_get(x_36, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_32, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_32, 2);
lean_inc(x_66);
lean_dec(x_32);
x_67 = !lean_is_exclusive(x_29);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_29, 0);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_nat_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_68, x_71);
lean_dec(x_68);
lean_ctor_set_tag(x_29, 0);
lean_ctor_set(x_29, 0, x_72);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_29);
x_74 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_75 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_73, x_74, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_array_get_size(x_65);
x_79 = lean_nat_dec_lt(x_69, x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_82 = l_outOfBounds___rarg(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_83, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_86 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Compiler_LCNF_eraseParams(x_65, x_5, x_6, x_7, x_8, x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_65);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_ctor_set(x_36, 1, x_87);
lean_ctor_set(x_36, 0, x_76);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_89, 0, x_20);
return x_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
lean_ctor_set(x_36, 1, x_87);
lean_ctor_set(x_36, 0, x_76);
lean_ctor_set(x_20, 0, x_36);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_20);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_76);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
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
lean_dec(x_76);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_76, 0);
lean_inc(x_102);
x_103 = lean_array_fget(x_65, x_69);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_104, x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
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
x_107 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Compiler_LCNF_eraseParams(x_65, x_5, x_6, x_7, x_8, x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_65);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
lean_ctor_set(x_36, 1, x_108);
lean_ctor_set(x_36, 0, x_76);
lean_ctor_set(x_20, 0, x_36);
lean_ctor_set(x_110, 0, x_20);
return x_110;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
lean_ctor_set(x_36, 1, x_108);
lean_ctor_set(x_36, 0, x_76);
lean_ctor_set(x_20, 0, x_36);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_20);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_76);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_115 = !lean_is_exclusive(x_107);
if (x_115 == 0)
{
return x_107;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_107, 0);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_107);
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
lean_dec(x_76);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
uint8_t x_123; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_75);
if (x_123 == 0)
{
return x_75;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_75, 0);
x_125 = lean_ctor_get(x_75, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_75);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_free_object(x_29);
lean_dec(x_68);
lean_dec(x_65);
lean_free_object(x_36);
x_127 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_ctor_set(x_20, 0, x_129);
lean_ctor_set(x_127, 0, x_20);
return x_127;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_127, 0);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_127);
lean_ctor_set(x_20, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_20);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
else
{
uint8_t x_133; 
lean_free_object(x_20);
x_133 = !lean_is_exclusive(x_127);
if (x_133 == 0)
{
return x_127;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_127, 0);
x_135 = lean_ctor_get(x_127, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_127);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_29, 0);
lean_inc(x_137);
lean_dec(x_29);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_eq(x_137, x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_137, x_140);
lean_dec(x_137);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_145 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_143, x_144, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_array_get_size(x_65);
x_149 = lean_nat_dec_lt(x_138, x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_146, 0);
lean_inc(x_150);
x_151 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_152 = l_outOfBounds___rarg(x_151);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec(x_152);
x_154 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_153, x_150, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_156 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Compiler_LCNF_eraseParams(x_65, x_5, x_6, x_7, x_8, x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_65);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
lean_ctor_set(x_36, 1, x_157);
lean_ctor_set(x_36, 0, x_146);
lean_ctor_set(x_20, 0, x_36);
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_20);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_146);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_156, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_165 = x_156;
} else {
 lean_dec_ref(x_156);
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
lean_dec(x_146);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_ctor_get(x_154, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_154, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_169 = x_154;
} else {
 lean_dec_ref(x_154);
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
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_146, 0);
lean_inc(x_171);
x_172 = lean_array_fget(x_65, x_138);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_174 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_173, x_171, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_176 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = l_Lean_Compiler_LCNF_eraseParams(x_65, x_5, x_6, x_7, x_8, x_178);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_65);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
lean_ctor_set(x_36, 1, x_177);
lean_ctor_set(x_36, 0, x_146);
lean_ctor_set(x_20, 0, x_36);
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_20);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_146);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_183 = lean_ctor_get(x_176, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_176, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_185 = x_176;
} else {
 lean_dec_ref(x_176);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_146);
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = lean_ctor_get(x_174, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_174, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_189 = x_174;
} else {
 lean_dec_ref(x_174);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_66);
lean_dec(x_65);
lean_free_object(x_36);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_145, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_145, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_193 = x_145;
} else {
 lean_dec_ref(x_145);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; 
lean_dec(x_137);
lean_dec(x_65);
lean_free_object(x_36);
x_195 = l_Lean_Compiler_LCNF_Simp_simp(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
lean_ctor_set(x_20, 0, x_196);
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_20);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_free_object(x_20);
x_200 = lean_ctor_get(x_195, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_195, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_204 = lean_ctor_get(x_36, 1);
lean_inc(x_204);
lean_dec(x_36);
x_205 = lean_ctor_get(x_32, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_32, 2);
lean_inc(x_206);
lean_dec(x_32);
x_207 = lean_ctor_get(x_29, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_208 = x_29;
} else {
 lean_dec_ref(x_29);
 x_208 = lean_box(0);
}
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_eq(x_207, x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_nat_sub(x_207, x_211);
lean_dec(x_207);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_208;
 lean_ctor_set_tag(x_213, 0);
}
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_213);
x_215 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_216 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_214, x_215, x_5, x_6, x_7, x_8, x_204);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = lean_array_get_size(x_205);
x_220 = lean_nat_dec_lt(x_209, x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_217, 0);
lean_inc(x_221);
x_222 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_223 = l_outOfBounds___rarg(x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_224, x_221, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_227 = l_Lean_Compiler_LCNF_Simp_simp(x_206, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Compiler_LCNF_eraseParams(x_205, x_5, x_6, x_7, x_8, x_229);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_205);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_217);
lean_ctor_set(x_233, 1, x_228);
lean_ctor_set(x_20, 0, x_233);
if (lean_is_scalar(x_232)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_232;
}
lean_ctor_set(x_234, 0, x_20);
lean_ctor_set(x_234, 1, x_231);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_217);
lean_dec(x_205);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_235 = lean_ctor_get(x_227, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_237 = x_227;
} else {
 lean_dec_ref(x_227);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_217);
lean_dec(x_206);
lean_dec(x_205);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_239 = lean_ctor_get(x_225, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_225, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_241 = x_225;
} else {
 lean_dec_ref(x_225);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_217, 0);
lean_inc(x_243);
x_244 = lean_array_fget(x_205, x_209);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
x_246 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_245, x_243, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_218);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_248 = l_Lean_Compiler_LCNF_Simp_simp(x_206, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Lean_Compiler_LCNF_eraseParams(x_205, x_5, x_6, x_7, x_8, x_250);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_205);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_217);
lean_ctor_set(x_254, 1, x_249);
lean_ctor_set(x_20, 0, x_254);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_20);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_217);
lean_dec(x_205);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_256 = lean_ctor_get(x_248, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_258 = x_248;
} else {
 lean_dec_ref(x_248);
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
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_217);
lean_dec(x_206);
lean_dec(x_205);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_260 = lean_ctor_get(x_246, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_246, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_262 = x_246;
} else {
 lean_dec_ref(x_246);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_206);
lean_dec(x_205);
lean_free_object(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_264 = lean_ctor_get(x_216, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_216, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_266 = x_216;
} else {
 lean_dec_ref(x_216);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_205);
x_268 = l_Lean_Compiler_LCNF_Simp_simp(x_206, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_204);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
lean_ctor_set(x_20, 0, x_269);
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_20);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_free_object(x_20);
x_273 = lean_ctor_get(x_268, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_275 = x_268;
} else {
 lean_dec_ref(x_268);
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
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_29);
x_277 = lean_ctor_get(x_36, 1);
lean_inc(x_277);
lean_dec(x_36);
x_278 = lean_ctor_get(x_32, 0);
lean_inc(x_278);
lean_dec(x_32);
x_279 = l_Lean_Compiler_LCNF_Simp_simp(x_278, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_277);
if (lean_obj_tag(x_279) == 0)
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; 
x_281 = lean_ctor_get(x_279, 0);
lean_ctor_set(x_20, 0, x_281);
lean_ctor_set(x_279, 0, x_20);
return x_279;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_279, 0);
x_283 = lean_ctor_get(x_279, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_279);
lean_ctor_set(x_20, 0, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_20);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
uint8_t x_285; 
lean_free_object(x_20);
x_285 = !lean_is_exclusive(x_279);
if (x_285 == 0)
{
return x_279;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_279, 0);
x_287 = lean_ctor_get(x_279, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_279);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_289 = lean_ctor_get(x_20, 0);
lean_inc(x_289);
lean_dec(x_20);
x_290 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_289);
x_291 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_290);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
lean_ctor_set_tag(x_16, 4);
lean_ctor_set(x_16, 0, x_293);
x_294 = l_Lean_Compiler_LCNF_eraseCode(x_16, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_16);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_295);
if (lean_obj_tag(x_292) == 0)
{
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; size_t x_306; size_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_ctor_get(x_292, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_292, 2);
lean_inc(x_299);
lean_dec(x_292);
x_300 = lean_ctor_get(x_289, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_289, 1);
lean_inc(x_301);
lean_dec(x_289);
x_302 = lean_ctor_get(x_300, 3);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_array_get_size(x_301);
x_304 = l_Array_toSubarray___rarg(x_301, x_302, x_303);
x_305 = lean_array_get_size(x_298);
x_306 = lean_usize_of_nat(x_305);
lean_dec(x_305);
x_307 = 0;
x_308 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_298, x_306, x_307, x_304, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_297);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_310 = l_Lean_Compiler_LCNF_Simp_simp(x_299, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_Compiler_LCNF_eraseParams(x_298, x_5, x_6, x_7, x_8, x_312);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_298);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_315 = x_313;
} else {
 lean_dec_ref(x_313);
 x_315 = lean_box(0);
}
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_311);
if (lean_is_scalar(x_315)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_315;
}
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_314);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_298);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_318 = lean_ctor_get(x_310, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_310, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_320 = x_310;
} else {
 lean_dec_ref(x_310);
 x_320 = lean_box(0);
}
if (lean_is_scalar(x_320)) {
 x_321 = lean_alloc_ctor(1, 2, 0);
} else {
 x_321 = x_320;
}
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_319);
return x_321;
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_322 = lean_ctor_get(x_296, 1);
lean_inc(x_322);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_323 = x_296;
} else {
 lean_dec_ref(x_296);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_292, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_292, 2);
lean_inc(x_325);
lean_dec(x_292);
x_326 = lean_ctor_get(x_289, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_327 = x_289;
} else {
 lean_dec_ref(x_289);
 x_327 = lean_box(0);
}
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_nat_dec_eq(x_326, x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_unsigned_to_nat(1u);
x_331 = lean_nat_sub(x_326, x_330);
lean_dec(x_326);
if (lean_is_scalar(x_327)) {
 x_332 = lean_alloc_ctor(0, 1, 0);
} else {
 x_332 = x_327;
 lean_ctor_set_tag(x_332, 0);
}
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
x_334 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_335 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_333, x_334, x_5, x_6, x_7, x_8, x_322);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_array_get_size(x_324);
x_339 = lean_nat_dec_lt(x_328, x_338);
lean_dec(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_336, 0);
lean_inc(x_340);
x_341 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_342 = l_outOfBounds___rarg(x_341);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec(x_342);
x_344 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_343, x_340, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_337);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_346 = l_Lean_Compiler_LCNF_Simp_simp(x_325, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_345);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
x_349 = l_Lean_Compiler_LCNF_eraseParams(x_324, x_5, x_6, x_7, x_8, x_348);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_324);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_323;
}
lean_ctor_set(x_352, 0, x_336);
lean_ctor_set(x_352, 1, x_347);
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_352);
if (lean_is_scalar(x_351)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_351;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_350);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_336);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_355 = lean_ctor_get(x_346, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_357 = x_346;
} else {
 lean_dec_ref(x_346);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_336);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_359 = lean_ctor_get(x_344, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_344, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_361 = x_344;
} else {
 lean_dec_ref(x_344);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_336, 0);
lean_inc(x_363);
x_364 = lean_array_fget(x_324, x_328);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_365, x_363, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_337);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_368 = l_Lean_Compiler_LCNF_Simp_simp(x_325, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = l_Lean_Compiler_LCNF_eraseParams(x_324, x_5, x_6, x_7, x_8, x_370);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_324);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_373 = x_371;
} else {
 lean_dec_ref(x_371);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_374 = lean_alloc_ctor(0, 2, 0);
} else {
 x_374 = x_323;
}
lean_ctor_set(x_374, 0, x_336);
lean_ctor_set(x_374, 1, x_369);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_372);
return x_376;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_336);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_377 = lean_ctor_get(x_368, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_368, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_379 = x_368;
} else {
 lean_dec_ref(x_368);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_336);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_381 = lean_ctor_get(x_366, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_366, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_383 = x_366;
} else {
 lean_dec_ref(x_366);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_385 = lean_ctor_get(x_335, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_335, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 x_387 = x_335;
} else {
 lean_dec_ref(x_335);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
lean_object* x_389; 
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_323);
x_389 = l_Lean_Compiler_LCNF_Simp_simp(x_325, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_322);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
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
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_390);
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
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_ctor_get(x_389, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_389, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_397 = x_389;
} else {
 lean_dec_ref(x_389);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_289);
x_399 = lean_ctor_get(x_296, 1);
lean_inc(x_399);
lean_dec(x_296);
x_400 = lean_ctor_get(x_292, 0);
lean_inc(x_400);
lean_dec(x_292);
x_401 = l_Lean_Compiler_LCNF_Simp_simp(x_400, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
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
x_405 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_405, 0, x_402);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_403);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_407 = lean_ctor_get(x_401, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_401, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_409 = x_401;
} else {
 lean_dec_ref(x_401);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_16, 0);
lean_inc(x_411);
lean_dec(x_16);
x_412 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(x_411, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_415 = x_412;
} else {
 lean_dec_ref(x_412);
 x_415 = lean_box(0);
}
x_416 = lean_box(0);
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_414);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_418 = lean_ctor_get(x_412, 1);
lean_inc(x_418);
lean_dec(x_412);
x_419 = lean_ctor_get(x_413, 0);
lean_inc(x_419);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 x_420 = x_413;
} else {
 lean_dec_ref(x_413);
 x_420 = lean_box(0);
}
x_421 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_419);
x_422 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_421);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
x_425 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_425, 0, x_424);
x_426 = l_Lean_Compiler_LCNF_eraseCode(x_425, x_5, x_6, x_7, x_8, x_418);
lean_dec(x_425);
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
lean_dec(x_426);
x_428 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_427);
if (lean_obj_tag(x_423) == 0)
{
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; size_t x_438; size_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_430 = lean_ctor_get(x_423, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_423, 2);
lean_inc(x_431);
lean_dec(x_423);
x_432 = lean_ctor_get(x_419, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_419, 1);
lean_inc(x_433);
lean_dec(x_419);
x_434 = lean_ctor_get(x_432, 3);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_array_get_size(x_433);
x_436 = l_Array_toSubarray___rarg(x_433, x_434, x_435);
x_437 = lean_array_get_size(x_430);
x_438 = lean_usize_of_nat(x_437);
lean_dec(x_437);
x_439 = 0;
x_440 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_430, x_438, x_439, x_436, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
x_441 = lean_ctor_get(x_440, 1);
lean_inc(x_441);
lean_dec(x_440);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_442 = l_Lean_Compiler_LCNF_Simp_simp(x_431, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = l_Lean_Compiler_LCNF_eraseParams(x_430, x_5, x_6, x_7, x_8, x_444);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_430);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_448 = x_420;
}
lean_ctor_set(x_448, 0, x_443);
if (lean_is_scalar(x_447)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_447;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_446);
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_430);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_450 = lean_ctor_get(x_442, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_442, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_452 = x_442;
} else {
 lean_dec_ref(x_442);
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
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
x_454 = lean_ctor_get(x_428, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_455 = x_428;
} else {
 lean_dec_ref(x_428);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_423, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_423, 2);
lean_inc(x_457);
lean_dec(x_423);
x_458 = lean_ctor_get(x_419, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_459 = x_419;
} else {
 lean_dec_ref(x_419);
 x_459 = lean_box(0);
}
x_460 = lean_unsigned_to_nat(0u);
x_461 = lean_nat_dec_eq(x_458, x_460);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_462 = lean_unsigned_to_nat(1u);
x_463 = lean_nat_sub(x_458, x_462);
lean_dec(x_458);
if (lean_is_scalar(x_459)) {
 x_464 = lean_alloc_ctor(0, 1, 0);
} else {
 x_464 = x_459;
 lean_ctor_set_tag(x_464, 0);
}
lean_ctor_set(x_464, 0, x_463);
x_465 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_465, 0, x_464);
x_466 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_467 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_465, x_466, x_5, x_6, x_7, x_8, x_454);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_array_get_size(x_456);
x_471 = lean_nat_dec_lt(x_460, x_470);
lean_dec(x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_472 = lean_ctor_get(x_468, 0);
lean_inc(x_472);
x_473 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_474 = l_outOfBounds___rarg(x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
lean_dec(x_474);
x_476 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_475, x_472, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_469);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
lean_dec(x_476);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_478 = l_Lean_Compiler_LCNF_Simp_simp(x_457, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
lean_dec(x_478);
x_481 = l_Lean_Compiler_LCNF_eraseParams(x_456, x_5, x_6, x_7, x_8, x_480);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_456);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 lean_ctor_release(x_481, 1);
 x_483 = x_481;
} else {
 lean_dec_ref(x_481);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_455;
}
lean_ctor_set(x_484, 0, x_468);
lean_ctor_set(x_484, 1, x_479);
if (lean_is_scalar(x_420)) {
 x_485 = lean_alloc_ctor(1, 1, 0);
} else {
 x_485 = x_420;
}
lean_ctor_set(x_485, 0, x_484);
if (lean_is_scalar(x_483)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_483;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_482);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_468);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_487 = lean_ctor_get(x_478, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_478, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_489 = x_478;
} else {
 lean_dec_ref(x_478);
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
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_468);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_491 = lean_ctor_get(x_476, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_476, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_493 = x_476;
} else {
 lean_dec_ref(x_476);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_495 = lean_ctor_get(x_468, 0);
lean_inc(x_495);
x_496 = lean_array_fget(x_456, x_460);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
lean_dec(x_496);
x_498 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_497, x_495, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_469);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_498, 1);
lean_inc(x_499);
lean_dec(x_498);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_500 = l_Lean_Compiler_LCNF_Simp_simp(x_457, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_503 = l_Lean_Compiler_LCNF_eraseParams(x_456, x_5, x_6, x_7, x_8, x_502);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_456);
x_504 = lean_ctor_get(x_503, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_503)) {
 lean_ctor_release(x_503, 0);
 lean_ctor_release(x_503, 1);
 x_505 = x_503;
} else {
 lean_dec_ref(x_503);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_455;
}
lean_ctor_set(x_506, 0, x_468);
lean_ctor_set(x_506, 1, x_501);
if (lean_is_scalar(x_420)) {
 x_507 = lean_alloc_ctor(1, 1, 0);
} else {
 x_507 = x_420;
}
lean_ctor_set(x_507, 0, x_506);
if (lean_is_scalar(x_505)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_505;
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_504);
return x_508;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_468);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_509 = lean_ctor_get(x_500, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_500, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_511 = x_500;
} else {
 lean_dec_ref(x_500);
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
lean_dec(x_468);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_513 = lean_ctor_get(x_498, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_498, 1);
lean_inc(x_514);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_515 = x_498;
} else {
 lean_dec_ref(x_498);
 x_515 = lean_box(0);
}
if (lean_is_scalar(x_515)) {
 x_516 = lean_alloc_ctor(1, 2, 0);
} else {
 x_516 = x_515;
}
lean_ctor_set(x_516, 0, x_513);
lean_ctor_set(x_516, 1, x_514);
return x_516;
}
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_420);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_517 = lean_ctor_get(x_467, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_467, 1);
lean_inc(x_518);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_519 = x_467;
} else {
 lean_dec_ref(x_467);
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
else
{
lean_object* x_521; 
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_456);
lean_dec(x_455);
x_521 = l_Lean_Compiler_LCNF_Simp_simp(x_457, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_454);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_524 = x_521;
} else {
 lean_dec_ref(x_521);
 x_524 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_525 = lean_alloc_ctor(1, 1, 0);
} else {
 x_525 = x_420;
}
lean_ctor_set(x_525, 0, x_522);
if (lean_is_scalar(x_524)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_524;
}
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_523);
return x_526;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_420);
x_527 = lean_ctor_get(x_521, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_521, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_529 = x_521;
} else {
 lean_dec_ref(x_521);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_529)) {
 x_530 = lean_alloc_ctor(1, 2, 0);
} else {
 x_530 = x_529;
}
lean_ctor_set(x_530, 0, x_527);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
}
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_419);
x_531 = lean_ctor_get(x_428, 1);
lean_inc(x_531);
lean_dec(x_428);
x_532 = lean_ctor_get(x_423, 0);
lean_inc(x_532);
lean_dec(x_423);
x_533 = l_Lean_Compiler_LCNF_Simp_simp(x_532, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_531);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_536 = x_533;
} else {
 lean_dec_ref(x_533);
 x_536 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_537 = lean_alloc_ctor(1, 1, 0);
} else {
 x_537 = x_420;
}
lean_ctor_set(x_537, 0, x_534);
if (lean_is_scalar(x_536)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_536;
}
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_535);
return x_538;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_420);
x_539 = lean_ctor_get(x_533, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_533, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_541 = x_533;
} else {
 lean_dec_ref(x_533);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_540);
return x_542;
}
}
}
}
}
else
{
lean_object* x_543; uint8_t x_544; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_543 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_544 = !lean_is_exclusive(x_543);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_543, 0);
x_546 = lean_alloc_ctor(1, 1, 0);
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
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_547);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
}
}
lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_15);
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
lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_14);
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__4(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_simp___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Compiler_LCNF_Simp_simp___lambda__7(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_2);
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
lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
