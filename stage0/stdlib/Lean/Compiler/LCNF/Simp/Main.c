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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_LCNF_Simp_simp___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParam___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
size_t lean_ptr_addr(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__1;
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at_Lean_Compiler_LCNF_Simp_simpFunDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at_Lean_Compiler_LCNF_Simp_simp___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_Lean_Compiler_LCNF_Simp_simp___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at_Lean_Compiler_LCNF_Simp_simp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___at_Lean_Compiler_LCNF_Simp_simp___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_uget(x_4, x_6);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_15);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_20, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_22, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
lean_ctor_set(x_20, 1, x_33);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = l_Lean_Compiler_LCNF_Arg_toExpr(x_31);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
x_39 = lean_array_get_size(x_38);
x_40 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
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
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_34, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_nat_add(x_37, x_32);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_35);
lean_ctor_set(x_55, 2, x_52);
x_56 = lean_array_uset(x_38, x_51, x_55);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_mul(x_54, x_57);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = lean_array_get_size(x_56);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; size_t x_64; 
x_63 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_56);
lean_ctor_set(x_21, 1, x_63);
lean_ctor_set(x_21, 0, x_54);
x_64 = lean_usize_add(x_6, x_49);
x_6 = x_64;
goto _start;
}
else
{
size_t x_66; 
lean_ctor_set(x_21, 1, x_56);
lean_ctor_set(x_21, 0, x_54);
x_66 = lean_usize_add(x_6, x_49);
x_6 = x_66;
goto _start;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; 
lean_inc(x_1);
x_68 = lean_array_uset(x_38, x_51, x_1);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_34, x_35, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
lean_ctor_set(x_21, 1, x_70);
x_71 = lean_usize_add(x_6, x_49);
x_6 = x_71;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_73 = lean_ctor_get(x_21, 0);
x_74 = lean_ctor_get(x_21, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_21);
x_75 = lean_array_get_size(x_74);
x_76 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_34);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_34, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_73, x_32);
lean_dec(x_73);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_34);
lean_ctor_set(x_91, 1, x_35);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_74, x_87, x_91);
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
lean_object* x_99; lean_object* x_100; size_t x_101; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_7, 1, x_100);
x_101 = lean_usize_add(x_6, x_85);
x_6 = x_101;
goto _start;
}
else
{
lean_object* x_103; size_t x_104; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_92);
lean_ctor_set(x_7, 1, x_103);
x_104 = lean_usize_add(x_6, x_85);
x_6 = x_104;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; 
lean_inc(x_1);
x_106 = lean_array_uset(x_74, x_87, x_1);
x_107 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_34, x_35, x_88);
x_108 = lean_array_uset(x_106, x_87, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_73);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_7, 1, x_109);
x_110 = lean_usize_add(x_6, x_85);
x_6 = x_110;
goto _start;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
lean_dec(x_20);
x_112 = lean_array_fget(x_22, x_23);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_add(x_23, x_113);
lean_dec(x_23);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_22);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_24);
x_116 = lean_ctor_get(x_18, 0);
lean_inc(x_116);
lean_dec(x_18);
x_117 = l_Lean_Compiler_LCNF_Arg_toExpr(x_112);
x_118 = lean_ctor_get(x_21, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_21, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_120 = x_21;
} else {
 lean_dec_ref(x_21);
 x_120 = lean_box(0);
}
x_121 = lean_array_get_size(x_119);
x_122 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_116);
x_123 = 32;
x_124 = lean_uint64_shift_right(x_122, x_123);
x_125 = lean_uint64_xor(x_122, x_124);
x_126 = 16;
x_127 = lean_uint64_shift_right(x_125, x_126);
x_128 = lean_uint64_xor(x_125, x_127);
x_129 = lean_uint64_to_usize(x_128);
x_130 = lean_usize_of_nat(x_121);
lean_dec(x_121);
x_131 = 1;
x_132 = lean_usize_sub(x_130, x_131);
x_133 = lean_usize_land(x_129, x_132);
x_134 = lean_array_uget(x_119, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_116, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_nat_add(x_118, x_113);
lean_dec(x_118);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_116);
lean_ctor_set(x_137, 1, x_117);
lean_ctor_set(x_137, 2, x_134);
x_138 = lean_array_uset(x_119, x_133, x_137);
x_139 = lean_unsigned_to_nat(4u);
x_140 = lean_nat_mul(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; size_t x_147; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_138);
if (lean_is_scalar(x_120)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_120;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set(x_7, 1, x_146);
lean_ctor_set(x_7, 0, x_115);
x_147 = lean_usize_add(x_6, x_131);
x_6 = x_147;
goto _start;
}
else
{
lean_object* x_149; size_t x_150; 
if (lean_is_scalar(x_120)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_120;
}
lean_ctor_set(x_149, 0, x_136);
lean_ctor_set(x_149, 1, x_138);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_115);
x_150 = lean_usize_add(x_6, x_131);
x_6 = x_150;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; size_t x_156; 
lean_inc(x_1);
x_152 = lean_array_uset(x_119, x_133, x_1);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_116, x_117, x_134);
x_154 = lean_array_uset(x_152, x_133, x_153);
if (lean_is_scalar(x_120)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_120;
}
lean_ctor_set(x_155, 0, x_118);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_7, 1, x_155);
lean_ctor_set(x_7, 0, x_115);
x_156 = lean_usize_add(x_6, x_131);
x_6 = x_156;
goto _start;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_7, 0);
x_159 = lean_ctor_get(x_7, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_7);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 2);
lean_inc(x_162);
x_163 = lean_nat_dec_lt(x_161, x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_18);
lean_dec(x_1);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_158);
lean_ctor_set(x_164, 1, x_159);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_15);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; size_t x_188; lean_object* x_189; uint8_t x_190; 
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 x_166 = x_158;
} else {
 lean_dec_ref(x_158);
 x_166 = lean_box(0);
}
x_167 = lean_array_fget(x_160, x_161);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_nat_add(x_161, x_168);
lean_dec(x_161);
if (lean_is_scalar(x_166)) {
 x_170 = lean_alloc_ctor(0, 3, 0);
} else {
 x_170 = x_166;
}
lean_ctor_set(x_170, 0, x_160);
lean_ctor_set(x_170, 1, x_169);
lean_ctor_set(x_170, 2, x_162);
x_171 = lean_ctor_get(x_18, 0);
lean_inc(x_171);
lean_dec(x_18);
x_172 = l_Lean_Compiler_LCNF_Arg_toExpr(x_167);
x_173 = lean_ctor_get(x_159, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_159, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_175 = x_159;
} else {
 lean_dec_ref(x_159);
 x_175 = lean_box(0);
}
x_176 = lean_array_get_size(x_174);
x_177 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_171);
x_178 = 32;
x_179 = lean_uint64_shift_right(x_177, x_178);
x_180 = lean_uint64_xor(x_177, x_179);
x_181 = 16;
x_182 = lean_uint64_shift_right(x_180, x_181);
x_183 = lean_uint64_xor(x_180, x_182);
x_184 = lean_uint64_to_usize(x_183);
x_185 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_186 = 1;
x_187 = lean_usize_sub(x_185, x_186);
x_188 = lean_usize_land(x_184, x_187);
x_189 = lean_array_uget(x_174, x_188);
x_190 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_171, x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_191 = lean_nat_add(x_173, x_168);
lean_dec(x_173);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_171);
lean_ctor_set(x_192, 1, x_172);
lean_ctor_set(x_192, 2, x_189);
x_193 = lean_array_uset(x_174, x_188, x_192);
x_194 = lean_unsigned_to_nat(4u);
x_195 = lean_nat_mul(x_191, x_194);
x_196 = lean_unsigned_to_nat(3u);
x_197 = lean_nat_div(x_195, x_196);
lean_dec(x_195);
x_198 = lean_array_get_size(x_193);
x_199 = lean_nat_dec_le(x_197, x_198);
lean_dec(x_198);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; size_t x_203; 
x_200 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_193);
if (lean_is_scalar(x_175)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_175;
}
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_170);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_usize_add(x_6, x_186);
x_6 = x_203;
x_7 = x_202;
goto _start;
}
else
{
lean_object* x_205; lean_object* x_206; size_t x_207; 
if (lean_is_scalar(x_175)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_175;
}
lean_ctor_set(x_205, 0, x_191);
lean_ctor_set(x_205, 1, x_193);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_170);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_usize_add(x_6, x_186);
x_6 = x_207;
x_7 = x_206;
goto _start;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; size_t x_214; 
lean_inc(x_1);
x_209 = lean_array_uset(x_174, x_188, x_1);
x_210 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_171, x_172, x_189);
x_211 = lean_array_uset(x_209, x_188, x_210);
if (lean_is_scalar(x_175)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_175;
}
lean_ctor_set(x_212, 0, x_173);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_170);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_usize_add(x_6, x_186);
x_6 = x_214;
x_7 = x_213;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_array_uget(x_16, x_4);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_dec(x_17);
x_22 = 1;
x_23 = l_Lean_Compiler_LCNF_replaceExprFVars(x_21, x_19, x_22, x_9, x_10, x_11, x_12, x_13);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
x_27 = l_Lean_Compiler_LCNF_mkAuxParam(x_24, x_26, x_9, x_10, x_11, x_12, x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_31 = lean_array_push(x_18, x_29);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Expr_fvar___override(x_32);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; size_t x_45; size_t x_46; size_t x_47; size_t x_48; size_t x_49; lean_object* x_50; uint8_t x_51; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
x_37 = lean_array_get_size(x_36);
x_38 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
x_39 = 32;
x_40 = lean_uint64_shift_right(x_38, x_39);
x_41 = lean_uint64_xor(x_38, x_40);
x_42 = 16;
x_43 = lean_uint64_shift_right(x_41, x_42);
x_44 = lean_uint64_xor(x_41, x_43);
x_45 = lean_uint64_to_usize(x_44);
x_46 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_47 = 1;
x_48 = lean_usize_sub(x_46, x_47);
x_49 = lean_usize_land(x_45, x_48);
x_50 = lean_array_uget(x_36, x_49);
x_51 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_20, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_35, x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_33);
lean_ctor_set(x_54, 2, x_50);
x_55 = lean_array_uset(x_36, x_49, x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_mul(x_53, x_56);
x_58 = lean_unsigned_to_nat(3u);
x_59 = lean_nat_div(x_57, x_58);
lean_dec(x_57);
x_60 = lean_array_get_size(x_55);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; size_t x_63; 
x_62 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_55);
lean_ctor_set(x_19, 1, x_62);
lean_ctor_set(x_19, 0, x_53);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 0, x_31);
x_63 = lean_usize_add(x_4, x_47);
x_4 = x_63;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
else
{
size_t x_65; 
lean_ctor_set(x_19, 1, x_55);
lean_ctor_set(x_19, 0, x_53);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 0, x_31);
x_65 = lean_usize_add(x_4, x_47);
x_4 = x_65;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; 
lean_inc(x_1);
x_67 = lean_array_uset(x_36, x_49, x_1);
x_68 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_20, x_33, x_50);
x_69 = lean_array_uset(x_67, x_49, x_68);
lean_ctor_set(x_19, 1, x_69);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 0, x_31);
x_70 = lean_usize_add(x_4, x_47);
x_4 = x_70;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_74 = lean_array_get_size(x_73);
x_75 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
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
x_87 = lean_array_uget(x_73, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_20, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_72, x_89);
lean_dec(x_72);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_20);
lean_ctor_set(x_91, 1, x_33);
lean_ctor_set(x_91, 2, x_87);
x_92 = lean_array_uset(x_73, x_86, x_91);
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
lean_object* x_99; lean_object* x_100; size_t x_101; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_27, 1, x_100);
lean_ctor_set(x_27, 0, x_31);
x_101 = lean_usize_add(x_4, x_84);
x_4 = x_101;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
else
{
lean_object* x_103; size_t x_104; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_92);
lean_ctor_set(x_27, 1, x_103);
lean_ctor_set(x_27, 0, x_31);
x_104 = lean_usize_add(x_4, x_84);
x_4 = x_104;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; size_t x_110; 
lean_inc(x_1);
x_106 = lean_array_uset(x_73, x_86, x_1);
x_107 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_20, x_33, x_87);
x_108 = lean_array_uset(x_106, x_86, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_72);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_27, 1, x_109);
lean_ctor_set(x_27, 0, x_31);
x_110 = lean_usize_add(x_4, x_84);
x_4 = x_110;
x_5 = x_27;
x_13 = x_30;
goto _start;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; size_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; lean_object* x_133; uint8_t x_134; 
x_112 = lean_ctor_get(x_27, 0);
x_113 = lean_ctor_get(x_27, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_27);
lean_inc(x_112);
x_114 = lean_array_push(x_18, x_112);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = l_Lean_Expr_fvar___override(x_115);
x_117 = lean_ctor_get(x_19, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_19, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_119 = x_19;
} else {
 lean_dec_ref(x_19);
 x_119 = lean_box(0);
}
x_120 = lean_array_get_size(x_118);
x_121 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
x_122 = 32;
x_123 = lean_uint64_shift_right(x_121, x_122);
x_124 = lean_uint64_xor(x_121, x_123);
x_125 = 16;
x_126 = lean_uint64_shift_right(x_124, x_125);
x_127 = lean_uint64_xor(x_124, x_126);
x_128 = lean_uint64_to_usize(x_127);
x_129 = lean_usize_of_nat(x_120);
lean_dec(x_120);
x_130 = 1;
x_131 = lean_usize_sub(x_129, x_130);
x_132 = lean_usize_land(x_128, x_131);
x_133 = lean_array_uget(x_118, x_132);
x_134 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_20, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_117, x_135);
lean_dec(x_117);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_20);
lean_ctor_set(x_137, 1, x_116);
lean_ctor_set(x_137, 2, x_133);
x_138 = lean_array_uset(x_118, x_132, x_137);
x_139 = lean_unsigned_to_nat(4u);
x_140 = lean_nat_mul(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_138);
if (lean_is_scalar(x_119)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_119;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_114);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_usize_add(x_4, x_130);
x_4 = x_148;
x_5 = x_147;
x_13 = x_113;
goto _start;
}
else
{
lean_object* x_150; lean_object* x_151; size_t x_152; 
if (lean_is_scalar(x_119)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_119;
}
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_138);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_114);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_usize_add(x_4, x_130);
x_4 = x_152;
x_5 = x_151;
x_13 = x_113;
goto _start;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; 
lean_inc(x_1);
x_154 = lean_array_uset(x_118, x_132, x_1);
x_155 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_20, x_116, x_133);
x_156 = lean_array_uset(x_154, x_132, x_155);
if (lean_is_scalar(x_119)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_119;
}
lean_ctor_set(x_157, 0, x_117);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_114);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_usize_add(x_4, x_130);
x_4 = x_159;
x_5 = x_158;
x_13 = x_113;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_12);
x_14 = l_Array_toSubarray___rarg(x_11, x_13, x_12);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_size(x_15);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_10, x_15, x_16, x_15, x_19, x_20, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_array_get_size(x_15);
x_27 = l_Array_toSubarray___rarg(x_15, x_12, x_26);
x_28 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
lean_ctor_set(x_22, 0, x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_10, x_27, x_30, x_32, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Compiler_LCNF_Code_internalize(x_38, x_37, x_5, x_6, x_7, x_8, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 0;
lean_inc(x_40);
x_43 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_40, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_46 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_36, x_40, x_45, x_5, x_6, x_7, x_8, x_44);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_40);
lean_dec(x_36);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; lean_object* x_58; size_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_dec(x_22);
x_52 = lean_array_get_size(x_15);
x_53 = l_Array_toSubarray___rarg(x_15, x_12, x_52);
x_54 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = lean_ctor_get(x_53, 2);
lean_inc(x_56);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
x_59 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_60 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_10, x_53, x_57, x_59, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_53);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_dec(x_1);
x_66 = l_Lean_Compiler_LCNF_Code_internalize(x_65, x_64, x_5, x_6, x_7, x_8, x_62);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = 0;
lean_inc(x_67);
x_70 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_67, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_73 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_63, x_67, x_72, x_5, x_6, x_7, x_8, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_63);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_Simp_specializePartialApp___spec__2(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_16;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 0);
if (x_11 == 0)
{
lean_object* x_211; 
x_211 = lean_box(0);
x_12 = x_211;
x_13 = x_9;
goto block_210;
}
else
{
lean_object* x_212; 
x_212 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_12 = x_212;
x_13 = x_9;
goto block_210;
}
block_210:
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
x_26 = l_Lean_Environment_find_x3f(x_25, x_17);
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
uint8_t x_206; 
x_206 = 0;
x_32 = x_206;
goto block_205;
}
else
{
uint8_t x_207; 
x_207 = 1;
x_32 = x_207;
goto block_205;
}
block_205:
{
lean_object* x_33; lean_object* x_34; 
if (x_32 == 0)
{
lean_object* x_203; 
x_203 = lean_box(0);
x_33 = x_203;
x_34 = x_23;
goto block_202;
}
else
{
lean_object* x_204; 
x_204 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_33 = x_204;
x_34 = x_23;
goto block_202;
}
block_202:
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_199; 
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
x_199 = lean_unbox(x_38);
lean_dec(x_38);
if (x_199 == 0)
{
uint8_t x_200; 
x_200 = 1;
x_41 = x_200;
goto block_198;
}
else
{
uint8_t x_201; 
x_201 = 0;
x_41 = x_201;
goto block_198;
}
block_198:
{
uint8_t x_42; 
if (x_41 == 0)
{
uint8_t x_196; 
x_196 = 0;
x_42 = x_196;
goto block_195;
}
else
{
uint8_t x_197; 
x_197 = 1;
x_42 = x_197;
goto block_195;
}
block_195:
{
lean_object* x_43; lean_object* x_44; 
if (x_42 == 0)
{
lean_object* x_193; 
x_193 = lean_box(0);
x_43 = x_193;
x_44 = x_39;
goto block_192;
}
else
{
lean_object* x_194; 
x_194 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_43 = x_194;
x_44 = x_39;
goto block_192;
}
block_192:
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
lean_object* x_190; 
x_190 = lean_box(0);
x_62 = x_190;
x_63 = x_55;
goto block_189;
}
else
{
lean_object* x_191; 
x_191 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__3;
x_62 = x_191;
x_63 = x_55;
goto block_189;
}
block_189:
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
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_array_size(x_71);
x_74 = 0;
lean_inc(x_71);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_73, x_74, x_71);
x_76 = l_Array_append___rarg(x_19, x_75);
lean_dec(x_75);
if (lean_is_scalar(x_20)) {
 x_77 = lean_alloc_ctor(3, 3, 0);
} else {
 x_77 = x_20;
}
lean_ctor_set(x_77, 0, x_17);
lean_ctor_set(x_77, 1, x_18);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_77, x_78, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
if (lean_is_scalar(x_58)) {
 x_83 = lean_alloc_ctor(5, 1, 0);
} else {
 x_83 = x_58;
 lean_ctor_set_tag(x_83, 5);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_69, 1, x_83);
lean_ctor_set(x_69, 0, x_80);
x_84 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_85 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_71, x_69, x_84, x_5, x_6, x_7, x_8, x_81);
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
lean_ctor_set(x_62, 0, x_86);
lean_ctor_set(x_92, 0, x_62);
return x_92;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_ctor_set(x_62, 0, x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_62);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_86);
lean_free_object(x_62);
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
lean_free_object(x_62);
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
lean_free_object(x_69);
lean_dec(x_71);
lean_free_object(x_62);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_79);
if (x_105 == 0)
{
return x_79;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_79, 0);
x_107 = lean_ctor_get(x_79, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_79);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_109 = lean_ctor_get(x_69, 0);
x_110 = lean_ctor_get(x_69, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_69);
x_111 = lean_array_size(x_109);
x_112 = 0;
lean_inc(x_109);
x_113 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_111, x_112, x_109);
x_114 = l_Array_append___rarg(x_19, x_113);
lean_dec(x_113);
if (lean_is_scalar(x_20)) {
 x_115 = lean_alloc_ctor(3, 3, 0);
} else {
 x_115 = x_20;
}
lean_ctor_set(x_115, 0, x_17);
lean_ctor_set(x_115, 1, x_18);
lean_ctor_set(x_115, 2, x_114);
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
if (lean_is_scalar(x_58)) {
 x_121 = lean_alloc_ctor(5, 1, 0);
} else {
 x_121 = x_58;
 lean_ctor_set_tag(x_121, 5);
}
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
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
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
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
lean_ctor_set(x_62, 0, x_125);
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_62);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_135 = lean_ctor_get(x_129, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_129, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_137 = x_129;
} else {
 lean_dec_ref(x_129);
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
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_free_object(x_62);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_139 = lean_ctor_get(x_124, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_141 = x_124;
} else {
 lean_dec_ref(x_124);
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
lean_dec(x_109);
lean_free_object(x_62);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_143 = lean_ctor_get(x_117, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_117, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_145 = x_117;
} else {
 lean_dec_ref(x_117);
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
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; size_t x_152; size_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_62);
x_147 = lean_ctor_get(x_1, 2);
lean_inc(x_147);
x_148 = l_Lean_Compiler_LCNF_mkNewParams(x_147, x_5, x_6, x_7, x_8, x_63);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_array_size(x_149);
x_153 = 0;
lean_inc(x_149);
x_154 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___spec__5(x_152, x_153, x_149);
x_155 = l_Array_append___rarg(x_19, x_154);
lean_dec(x_154);
if (lean_is_scalar(x_20)) {
 x_156 = lean_alloc_ctor(3, 3, 0);
} else {
 x_156 = x_20;
}
lean_ctor_set(x_156, 0, x_17);
lean_ctor_set(x_156, 1, x_18);
lean_ctor_set(x_156, 2, x_155);
x_157 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_158 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_156, x_157, x_5, x_6, x_7, x_8, x_150);
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
if (lean_is_scalar(x_58)) {
 x_162 = lean_alloc_ctor(5, 1, 0);
} else {
 x_162 = x_58;
 lean_ctor_set_tag(x_162, 5);
}
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_151)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_151;
}
lean_ctor_set(x_163, 0, x_159);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_165 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_149, x_163, x_164, x_5, x_6, x_7, x_8, x_160);
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
x_170 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_168, x_169, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_167);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_175 = lean_alloc_ctor(1, 1, 0);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_58);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_208; lean_object* x_209; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_13);
return x_209;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_array_mk(x_11);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_jp", 3, 3);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_371; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_371 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_371 == 0)
{
lean_object* x_372; 
x_372 = lean_box(0);
x_38 = x_372;
goto block_370;
}
else
{
uint8_t x_373; 
x_373 = lean_nat_dec_eq(x_24, x_27);
if (x_373 == 0)
{
lean_object* x_374; 
x_374 = lean_box(0);
x_38 = x_374;
goto block_370;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_375 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_377 = l_Lean_Compiler_LCNF_Simp_simp(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_376);
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_378; 
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_377, 0, x_380);
return x_377;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_381 = lean_ctor_get(x_377, 0);
x_382 = lean_ctor_get(x_377, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_377);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_381);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
uint8_t x_385; 
x_385 = !lean_is_exclusive(x_377);
if (x_385 == 0)
{
return x_377;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_377, 0);
x_387 = lean_ctor_get(x_377, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_377);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
block_370:
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_21, 2);
lean_inc(x_47);
lean_dec(x_21);
x_48 = l_Lean_Compiler_LCNF_inferAppType(x_47, x_33, x_6, x_7, x_8, x_9, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
lean_inc(x_49);
x_52 = l_Lean_Expr_headBeta(x_49);
x_53 = l_Lean_Expr_isForall(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_54 = l_Lean_Compiler_LCNF_mkAuxParam(x_49, x_34, x_6, x_7, x_8, x_9, x_50);
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
lean_object* x_89; 
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_89 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_91 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_60 = x_92;
x_61 = x_93;
goto block_88;
}
else
{
uint8_t x_94; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
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
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_51);
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
x_98 = !lean_is_exclusive(x_89);
if (x_98 == 0)
{
return x_89;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_89, 0);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_89);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_array_get_size(x_23);
x_103 = l_Array_toSubarray___rarg(x_23, x_27, x_102);
x_104 = l_Array_ofSubarray___rarg(x_103);
lean_dec(x_103);
lean_ctor_set_tag(x_43, 4);
lean_ctor_set(x_43, 1, x_104);
lean_ctor_set(x_43, 0, x_58);
x_105 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_106 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_43, x_105, x_6, x_7, x_8, x_9, x_56);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
x_110 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_113 = l_Lean_Compiler_LCNF_Simp_simp(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_60 = x_114;
x_61 = x_115;
goto block_88;
}
else
{
uint8_t x_116; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_116 = !lean_is_exclusive(x_113);
if (x_116 == 0)
{
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 0);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_113);
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
lean_dec(x_107);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_51);
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
x_120 = !lean_is_exclusive(x_110);
if (x_120 == 0)
{
return x_110;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_110, 0);
x_122 = lean_ctor_get(x_110, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_110);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_51);
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
x_124 = !lean_is_exclusive(x_106);
if (x_124 == 0)
{
return x_106;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_106, 0);
x_126 = lean_ctor_get(x_106, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_106);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
block_88:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_57;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_mk(x_63);
x_65 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_66 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_64, x_60, x_65, x_6, x_7, x_8, x_9, x_61);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_62);
x_70 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_69, x_6, x_7, x_8, x_9, x_68);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 0);
if (lean_is_scalar(x_51)) {
 x_73 = lean_alloc_ctor(2, 2, 0);
} else {
 x_73 = x_51;
 lean_ctor_set_tag(x_73, 2);
}
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
if (lean_is_scalar(x_51)) {
 x_77 = lean_alloc_ctor(2, 2, 0);
} else {
 x_77 = x_51;
 lean_ctor_set_tag(x_77, 2);
}
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
lean_dec(x_51);
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
lean_dec(x_51);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_49);
x_128 = lean_box(0);
x_129 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_130 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_131 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_129, x_40, x_130, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_134 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_132, x_6, x_7, x_8, x_9, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_138 == 0)
{
lean_object* x_153; 
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_23);
x_153 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_137, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_136);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_155 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_139 = x_156;
x_140 = x_157;
goto block_152;
}
else
{
uint8_t x_158; 
lean_dec(x_135);
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_135);
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_153);
if (x_162 == 0)
{
return x_153;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_153, 0);
x_164 = lean_ctor_get(x_153, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_153);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_array_get_size(x_23);
x_167 = l_Array_toSubarray___rarg(x_23, x_27, x_166);
x_168 = l_Array_ofSubarray___rarg(x_167);
lean_dec(x_167);
lean_ctor_set_tag(x_43, 4);
lean_ctor_set(x_43, 1, x_168);
lean_ctor_set(x_43, 0, x_137);
x_169 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_170 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_43, x_169, x_6, x_7, x_8, x_9, x_136);
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
x_139 = x_178;
x_140 = x_179;
goto block_152;
}
else
{
uint8_t x_180; 
lean_dec(x_135);
lean_dec(x_51);
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
lean_dec(x_135);
lean_dec(x_51);
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
lean_dec(x_135);
lean_dec(x_51);
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
block_152:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_135);
if (lean_is_scalar(x_51)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_51;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_128);
x_143 = lean_array_mk(x_142);
x_144 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_143, x_139, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_143);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
if (lean_is_scalar(x_22)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_22;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_144, 0);
x_149 = lean_ctor_get(x_144, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_144);
if (lean_is_scalar(x_22)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_22;
}
lean_ctor_set(x_150, 0, x_148);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_51);
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
x_192 = !lean_is_exclusive(x_134);
if (x_192 == 0)
{
return x_134;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_134, 0);
x_194 = lean_ctor_get(x_134, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_134);
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
lean_dec(x_51);
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
x_196 = !lean_is_exclusive(x_131);
if (x_196 == 0)
{
return x_131;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_131, 0);
x_198 = lean_ctor_get(x_131, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_131);
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
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_200 = lean_ctor_get(x_43, 1);
lean_inc(x_200);
lean_dec(x_43);
x_201 = lean_ctor_get(x_21, 2);
lean_inc(x_201);
lean_dec(x_21);
x_202 = l_Lean_Compiler_LCNF_inferAppType(x_201, x_33, x_6, x_7, x_8, x_9, x_200);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
lean_inc(x_203);
x_206 = l_Lean_Expr_headBeta(x_203);
x_207 = l_Lean_Expr_isForall(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; 
x_208 = l_Lean_Compiler_LCNF_mkAuxParam(x_203, x_34, x_6, x_7, x_8, x_9, x_204);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_209, 0);
lean_inc(x_212);
x_213 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_213 == 0)
{
lean_object* x_240; 
lean_dec(x_27);
lean_dec(x_23);
x_240 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_212, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_210);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_242 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_214 = x_243;
x_215 = x_244;
goto block_239;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_242, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_247 = x_242;
} else {
 lean_dec_ref(x_242);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
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
x_249 = lean_ctor_get(x_240, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_240, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_251 = x_240;
} else {
 lean_dec_ref(x_240);
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
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_253 = lean_array_get_size(x_23);
x_254 = l_Array_toSubarray___rarg(x_23, x_27, x_253);
x_255 = l_Array_ofSubarray___rarg(x_254);
lean_dec(x_254);
x_256 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_256, 0, x_212);
lean_ctor_set(x_256, 1, x_255);
x_257 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_258 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_256, x_257, x_6, x_7, x_8, x_9, x_210);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
x_262 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_261, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_259);
lean_ctor_set(x_264, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_265 = l_Lean_Compiler_LCNF_Simp_simp(x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_263);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_214 = x_266;
x_215 = x_267;
goto block_239;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
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
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_259);
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
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
x_272 = lean_ctor_get(x_262, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_262, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_274 = x_262;
} else {
 lean_dec_ref(x_262);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_205);
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
x_276 = lean_ctor_get(x_258, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_258, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_278 = x_258;
} else {
 lean_dec_ref(x_258);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
block_239:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_box(0);
if (lean_is_scalar(x_211)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_211;
 lean_ctor_set_tag(x_217, 1);
}
lean_ctor_set(x_217, 0, x_209);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_array_mk(x_217);
x_219 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_220 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_218, x_214, x_219, x_6, x_7, x_8, x_9, x_215);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_221);
x_223 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_223, 0, x_221);
lean_closure_set(x_223, 1, x_216);
x_224 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_223, x_6, x_7, x_8, x_9, x_222);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
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
if (lean_is_scalar(x_205)) {
 x_228 = lean_alloc_ctor(2, 2, 0);
} else {
 x_228 = x_205;
 lean_ctor_set_tag(x_228, 2);
}
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set(x_228, 1, x_225);
if (lean_is_scalar(x_22)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_22;
}
lean_ctor_set(x_229, 0, x_228);
if (lean_is_scalar(x_227)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_227;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_226);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_221);
lean_dec(x_205);
lean_dec(x_22);
x_231 = lean_ctor_get(x_224, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_233 = x_224;
} else {
 lean_dec_ref(x_224);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_205);
lean_dec(x_40);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_235 = lean_ctor_get(x_220, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_237 = x_220;
} else {
 lean_dec_ref(x_220);
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
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_203);
x_280 = lean_box(0);
x_281 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_282 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_283 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_281, x_40, x_282, x_6, x_7, x_8, x_9, x_204);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_286 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_284, x_6, x_7, x_8, x_9, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
x_290 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_290 == 0)
{
lean_object* x_303; 
lean_dec(x_27);
lean_dec(x_23);
x_303 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_289, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_288);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_305 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_291 = x_306;
x_292 = x_307;
goto block_302;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_287);
lean_dec(x_205);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_310 = x_305;
} else {
 lean_dec_ref(x_305);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_287);
lean_dec(x_205);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_312 = lean_ctor_get(x_303, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_303, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_314 = x_303;
} else {
 lean_dec_ref(x_303);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_316 = lean_array_get_size(x_23);
x_317 = l_Array_toSubarray___rarg(x_23, x_27, x_316);
x_318 = l_Array_ofSubarray___rarg(x_317);
lean_dec(x_317);
x_319 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_319, 0, x_289);
lean_ctor_set(x_319, 1, x_318);
x_320 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_321 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_319, x_320, x_6, x_7, x_8, x_9, x_288);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_ctor_get(x_322, 0);
lean_inc(x_324);
x_325 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_324, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_323);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_322);
lean_ctor_set(x_327, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_328 = l_Lean_Compiler_LCNF_Simp_simp(x_327, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_326);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_291 = x_329;
x_292 = x_330;
goto block_302;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_287);
lean_dec(x_205);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_331 = lean_ctor_get(x_328, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_333 = x_328;
} else {
 lean_dec_ref(x_328);
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
lean_dec(x_322);
lean_dec(x_287);
lean_dec(x_205);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_335 = lean_ctor_get(x_325, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_325, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_337 = x_325;
} else {
 lean_dec_ref(x_325);
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
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_287);
lean_dec(x_205);
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
x_339 = lean_ctor_get(x_321, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_321, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_341 = x_321;
} else {
 lean_dec_ref(x_321);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_339);
lean_ctor_set(x_342, 1, x_340);
return x_342;
}
}
block_302:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_287);
if (lean_is_scalar(x_205)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_205;
 lean_ctor_set_tag(x_294, 1);
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_280);
x_295 = lean_array_mk(x_294);
x_296 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_295, x_291, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_292);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_22;
}
lean_ctor_set(x_300, 0, x_297);
if (lean_is_scalar(x_299)) {
 x_301 = lean_alloc_ctor(0, 2, 0);
} else {
 x_301 = x_299;
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_298);
return x_301;
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_205);
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
x_343 = lean_ctor_get(x_286, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_286, 1);
lean_inc(x_344);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_345 = x_286;
} else {
 lean_dec_ref(x_286);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 2, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_343);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_205);
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
x_347 = lean_ctor_get(x_283, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_283, 1);
lean_inc(x_348);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_349 = x_283;
} else {
 lean_dec_ref(x_283);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_348);
return x_350;
}
}
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_33);
lean_dec(x_21);
x_351 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_41);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
x_353 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_353, 0, x_3);
lean_closure_set(x_353, 1, x_4);
lean_closure_set(x_353, 2, x_5);
lean_closure_set(x_353, 3, x_27);
lean_closure_set(x_353, 4, x_24);
lean_closure_set(x_353, 5, x_26);
lean_closure_set(x_353, 6, x_2);
lean_closure_set(x_353, 7, x_23);
x_354 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_40, x_353, x_6, x_7, x_8, x_9, x_352);
if (lean_obj_tag(x_354) == 0)
{
uint8_t x_355; 
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_354, 0);
if (lean_is_scalar(x_22)) {
 x_357 = lean_alloc_ctor(1, 1, 0);
} else {
 x_357 = x_22;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_354, 0, x_357);
return x_354;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_358 = lean_ctor_get(x_354, 0);
x_359 = lean_ctor_get(x_354, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_354);
if (lean_is_scalar(x_22)) {
 x_360 = lean_alloc_ctor(1, 1, 0);
} else {
 x_360 = x_22;
}
lean_ctor_set(x_360, 0, x_358);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
else
{
uint8_t x_362; 
lean_dec(x_22);
x_362 = !lean_is_exclusive(x_354);
if (x_362 == 0)
{
return x_354;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_354, 0);
x_364 = lean_ctor_get(x_354, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_354);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
}
else
{
uint8_t x_366; 
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
x_366 = !lean_is_exclusive(x_39);
if (x_366 == 0)
{
return x_39;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_39, 0);
x_368 = lean_ctor_get(x_39, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_39);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
}
else
{
uint8_t x_389; 
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
x_389 = !lean_is_exclusive(x_35);
if (x_389 == 0)
{
return x_35;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_35, 0);
x_391 = lean_ctor_get(x_35, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_35);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
case 1:
{
uint8_t x_393; lean_object* x_394; 
x_393 = 0;
lean_inc(x_33);
x_394 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_393, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_730; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_730 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_730 == 0)
{
lean_object* x_731; 
x_731 = lean_box(0);
x_397 = x_731;
goto block_729;
}
else
{
uint8_t x_732; 
x_732 = lean_nat_dec_eq(x_24, x_27);
if (x_732 == 0)
{
lean_object* x_733; 
x_733 = lean_box(0);
x_397 = x_733;
goto block_729;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_734 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_396);
x_735 = lean_ctor_get(x_734, 1);
lean_inc(x_735);
lean_dec(x_734);
x_736 = l_Lean_Compiler_LCNF_Simp_simp(x_395, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_735);
if (lean_obj_tag(x_736) == 0)
{
uint8_t x_737; 
x_737 = !lean_is_exclusive(x_736);
if (x_737 == 0)
{
lean_object* x_738; lean_object* x_739; 
x_738 = lean_ctor_get(x_736, 0);
x_739 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_736, 0, x_739);
return x_736;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_740 = lean_ctor_get(x_736, 0);
x_741 = lean_ctor_get(x_736, 1);
lean_inc(x_741);
lean_inc(x_740);
lean_dec(x_736);
x_742 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_742, 0, x_740);
x_743 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_741);
return x_743;
}
}
else
{
uint8_t x_744; 
x_744 = !lean_is_exclusive(x_736);
if (x_744 == 0)
{
return x_736;
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_745 = lean_ctor_get(x_736, 0);
x_746 = lean_ctor_get(x_736, 1);
lean_inc(x_746);
lean_inc(x_745);
lean_dec(x_736);
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_745);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
}
}
block_729:
{
lean_object* x_398; 
lean_dec(x_397);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_398 = l_Lean_Compiler_LCNF_Simp_simp(x_395, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_396);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_399);
x_401 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_399);
if (x_401 == 0)
{
lean_object* x_402; uint8_t x_403; 
x_402 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_400);
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_404 = lean_ctor_get(x_402, 1);
x_405 = lean_ctor_get(x_402, 0);
lean_dec(x_405);
x_406 = lean_ctor_get(x_21, 2);
lean_inc(x_406);
lean_dec(x_21);
x_407 = l_Lean_Compiler_LCNF_inferAppType(x_406, x_33, x_6, x_7, x_8, x_9, x_404);
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
x_411 = l_Lean_Expr_headBeta(x_408);
x_412 = l_Lean_Expr_isForall(x_411);
lean_dec(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; 
x_413 = l_Lean_Compiler_LCNF_mkAuxParam(x_408, x_393, x_6, x_7, x_8, x_9, x_409);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_413, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_413)) {
 lean_ctor_release(x_413, 0);
 lean_ctor_release(x_413, 1);
 x_416 = x_413;
} else {
 lean_dec_ref(x_413);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
x_418 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_418 == 0)
{
lean_object* x_448; 
lean_free_object(x_402);
lean_dec(x_27);
lean_dec(x_23);
x_448 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_417, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_415);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_450 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_449);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_450, 1);
lean_inc(x_452);
lean_dec(x_450);
x_419 = x_451;
x_420 = x_452;
goto block_447;
}
else
{
uint8_t x_453; 
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_453 = !lean_is_exclusive(x_450);
if (x_453 == 0)
{
return x_450;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_450, 0);
x_455 = lean_ctor_get(x_450, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_450);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
uint8_t x_457; 
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_457 = !lean_is_exclusive(x_448);
if (x_457 == 0)
{
return x_448;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_448, 0);
x_459 = lean_ctor_get(x_448, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_448);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_458);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_461 = lean_array_get_size(x_23);
x_462 = l_Array_toSubarray___rarg(x_23, x_27, x_461);
x_463 = l_Array_ofSubarray___rarg(x_462);
lean_dec(x_462);
lean_ctor_set_tag(x_402, 4);
lean_ctor_set(x_402, 1, x_463);
lean_ctor_set(x_402, 0, x_417);
x_464 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_465 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_402, x_464, x_6, x_7, x_8, x_9, x_415);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
x_469 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_468, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
lean_dec(x_469);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_466);
lean_ctor_set(x_471, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_472 = l_Lean_Compiler_LCNF_Simp_simp(x_471, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_470);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_472, 1);
lean_inc(x_474);
lean_dec(x_472);
x_419 = x_473;
x_420 = x_474;
goto block_447;
}
else
{
uint8_t x_475; 
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_475 = !lean_is_exclusive(x_472);
if (x_475 == 0)
{
return x_472;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_472, 0);
x_477 = lean_ctor_get(x_472, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_472);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_466);
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_416);
lean_dec(x_414);
lean_dec(x_410);
lean_dec(x_399);
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
block_447:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_421 = lean_box(0);
if (lean_is_scalar(x_416)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_416;
 lean_ctor_set_tag(x_422, 1);
}
lean_ctor_set(x_422, 0, x_414);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_array_mk(x_422);
x_424 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_425 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_423, x_419, x_424, x_6, x_7, x_8, x_9, x_420);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
lean_inc(x_426);
x_428 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_428, 0, x_426);
lean_closure_set(x_428, 1, x_421);
x_429 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_399, x_428, x_6, x_7, x_8, x_9, x_427);
if (lean_obj_tag(x_429) == 0)
{
uint8_t x_430; 
x_430 = !lean_is_exclusive(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_429, 0);
if (lean_is_scalar(x_410)) {
 x_432 = lean_alloc_ctor(2, 2, 0);
} else {
 x_432 = x_410;
 lean_ctor_set_tag(x_432, 2);
}
lean_ctor_set(x_432, 0, x_426);
lean_ctor_set(x_432, 1, x_431);
if (lean_is_scalar(x_22)) {
 x_433 = lean_alloc_ctor(1, 1, 0);
} else {
 x_433 = x_22;
}
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_429, 0, x_433);
return x_429;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_434 = lean_ctor_get(x_429, 0);
x_435 = lean_ctor_get(x_429, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_429);
if (lean_is_scalar(x_410)) {
 x_436 = lean_alloc_ctor(2, 2, 0);
} else {
 x_436 = x_410;
 lean_ctor_set_tag(x_436, 2);
}
lean_ctor_set(x_436, 0, x_426);
lean_ctor_set(x_436, 1, x_434);
if (lean_is_scalar(x_22)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_22;
}
lean_ctor_set(x_437, 0, x_436);
x_438 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_438, 0, x_437);
lean_ctor_set(x_438, 1, x_435);
return x_438;
}
}
else
{
uint8_t x_439; 
lean_dec(x_426);
lean_dec(x_410);
lean_dec(x_22);
x_439 = !lean_is_exclusive(x_429);
if (x_439 == 0)
{
return x_429;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_429, 0);
x_441 = lean_ctor_get(x_429, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_429);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_410);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_443 = !lean_is_exclusive(x_425);
if (x_443 == 0)
{
return x_425;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_425, 0);
x_445 = lean_ctor_get(x_425, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_425);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_408);
x_487 = lean_box(0);
x_488 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_489 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_490 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_488, x_399, x_489, x_6, x_7, x_8, x_9, x_409);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_493 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_491, x_6, x_7, x_8, x_9, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; lean_object* x_498; lean_object* x_499; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
x_497 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_497 == 0)
{
lean_object* x_512; 
lean_free_object(x_402);
lean_dec(x_27);
lean_dec(x_23);
x_512 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_496, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_495);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; 
x_513 = lean_ctor_get(x_512, 1);
lean_inc(x_513);
lean_dec(x_512);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_514 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_513);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_498 = x_515;
x_499 = x_516;
goto block_511;
}
else
{
uint8_t x_517; 
lean_dec(x_494);
lean_dec(x_410);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_517 = !lean_is_exclusive(x_514);
if (x_517 == 0)
{
return x_514;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_514, 0);
x_519 = lean_ctor_get(x_514, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_514);
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
lean_dec(x_494);
lean_dec(x_410);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_521 = !lean_is_exclusive(x_512);
if (x_521 == 0)
{
return x_512;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_512, 0);
x_523 = lean_ctor_get(x_512, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_512);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
return x_524;
}
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_525 = lean_array_get_size(x_23);
x_526 = l_Array_toSubarray___rarg(x_23, x_27, x_525);
x_527 = l_Array_ofSubarray___rarg(x_526);
lean_dec(x_526);
lean_ctor_set_tag(x_402, 4);
lean_ctor_set(x_402, 1, x_527);
lean_ctor_set(x_402, 0, x_496);
x_528 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_529 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_402, x_528, x_6, x_7, x_8, x_9, x_495);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_ctor_get(x_530, 0);
lean_inc(x_532);
x_533 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_532, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_531);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_530);
lean_ctor_set(x_535, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_536 = l_Lean_Compiler_LCNF_Simp_simp(x_535, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_534);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_498 = x_537;
x_499 = x_538;
goto block_511;
}
else
{
uint8_t x_539; 
lean_dec(x_494);
lean_dec(x_410);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_539 = !lean_is_exclusive(x_536);
if (x_539 == 0)
{
return x_536;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_536, 0);
x_541 = lean_ctor_get(x_536, 1);
lean_inc(x_541);
lean_inc(x_540);
lean_dec(x_536);
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_541);
return x_542;
}
}
}
else
{
uint8_t x_543; 
lean_dec(x_530);
lean_dec(x_494);
lean_dec(x_410);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_543 = !lean_is_exclusive(x_533);
if (x_543 == 0)
{
return x_533;
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = lean_ctor_get(x_533, 0);
x_545 = lean_ctor_get(x_533, 1);
lean_inc(x_545);
lean_inc(x_544);
lean_dec(x_533);
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
lean_dec(x_494);
lean_dec(x_410);
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
x_547 = !lean_is_exclusive(x_529);
if (x_547 == 0)
{
return x_529;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_529, 0);
x_549 = lean_ctor_get(x_529, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_529);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
block_511:
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; 
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_494);
if (lean_is_scalar(x_410)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_410;
 lean_ctor_set_tag(x_501, 1);
}
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_487);
x_502 = lean_array_mk(x_501);
x_503 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_502, x_498, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_499);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_502);
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_503, 0);
if (lean_is_scalar(x_22)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_22;
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_503, 0, x_506);
return x_503;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_503, 0);
x_508 = lean_ctor_get(x_503, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_503);
if (lean_is_scalar(x_22)) {
 x_509 = lean_alloc_ctor(1, 1, 0);
} else {
 x_509 = x_22;
}
lean_ctor_set(x_509, 0, x_507);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_410);
lean_free_object(x_402);
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
x_551 = !lean_is_exclusive(x_493);
if (x_551 == 0)
{
return x_493;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_493, 0);
x_553 = lean_ctor_get(x_493, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_493);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_410);
lean_free_object(x_402);
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
x_555 = !lean_is_exclusive(x_490);
if (x_555 == 0)
{
return x_490;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_490, 0);
x_557 = lean_ctor_get(x_490, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_490);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_559 = lean_ctor_get(x_402, 1);
lean_inc(x_559);
lean_dec(x_402);
x_560 = lean_ctor_get(x_21, 2);
lean_inc(x_560);
lean_dec(x_21);
x_561 = l_Lean_Compiler_LCNF_inferAppType(x_560, x_33, x_6, x_7, x_8, x_9, x_559);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_564 = x_561;
} else {
 lean_dec_ref(x_561);
 x_564 = lean_box(0);
}
lean_inc(x_562);
x_565 = l_Lean_Expr_headBeta(x_562);
x_566 = l_Lean_Expr_isForall(x_565);
lean_dec(x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; lean_object* x_574; 
x_567 = l_Lean_Compiler_LCNF_mkAuxParam(x_562, x_393, x_6, x_7, x_8, x_9, x_563);
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_567)) {
 lean_ctor_release(x_567, 0);
 lean_ctor_release(x_567, 1);
 x_570 = x_567;
} else {
 lean_dec_ref(x_567);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_568, 0);
lean_inc(x_571);
x_572 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_572 == 0)
{
lean_object* x_599; 
lean_dec(x_27);
lean_dec(x_23);
x_599 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_571, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_569);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
lean_dec(x_599);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_601 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_573 = x_602;
x_574 = x_603;
goto block_598;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_604 = lean_ctor_get(x_601, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_601, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_606 = x_601;
} else {
 lean_dec_ref(x_601);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_608 = lean_ctor_get(x_599, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_599, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_610 = x_599;
} else {
 lean_dec_ref(x_599);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_612 = lean_array_get_size(x_23);
x_613 = l_Array_toSubarray___rarg(x_23, x_27, x_612);
x_614 = l_Array_ofSubarray___rarg(x_613);
lean_dec(x_613);
x_615 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_615, 0, x_571);
lean_ctor_set(x_615, 1, x_614);
x_616 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_617 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_615, x_616, x_6, x_7, x_8, x_9, x_569);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_ctor_get(x_618, 0);
lean_inc(x_620);
x_621 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_620, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_619);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_618);
lean_ctor_set(x_623, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_624 = l_Lean_Compiler_LCNF_Simp_simp(x_623, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_622);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
x_573 = x_625;
x_574 = x_626;
goto block_598;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_627 = lean_ctor_get(x_624, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_624, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_629 = x_624;
} else {
 lean_dec_ref(x_624);
 x_629 = lean_box(0);
}
if (lean_is_scalar(x_629)) {
 x_630 = lean_alloc_ctor(1, 2, 0);
} else {
 x_630 = x_629;
}
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_628);
return x_630;
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_618);
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_631 = lean_ctor_get(x_621, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_621, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_633 = x_621;
} else {
 lean_dec_ref(x_621);
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
lean_dec(x_570);
lean_dec(x_568);
lean_dec(x_564);
lean_dec(x_399);
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
x_635 = lean_ctor_get(x_617, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_617, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_637 = x_617;
} else {
 lean_dec_ref(x_617);
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
block_598:
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = lean_box(0);
if (lean_is_scalar(x_570)) {
 x_576 = lean_alloc_ctor(1, 2, 0);
} else {
 x_576 = x_570;
 lean_ctor_set_tag(x_576, 1);
}
lean_ctor_set(x_576, 0, x_568);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_array_mk(x_576);
x_578 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_579 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_577, x_573, x_578, x_6, x_7, x_8, x_9, x_574);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
lean_inc(x_580);
x_582 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_582, 0, x_580);
lean_closure_set(x_582, 1, x_575);
x_583 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_399, x_582, x_6, x_7, x_8, x_9, x_581);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_586 = x_583;
} else {
 lean_dec_ref(x_583);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_564)) {
 x_587 = lean_alloc_ctor(2, 2, 0);
} else {
 x_587 = x_564;
 lean_ctor_set_tag(x_587, 2);
}
lean_ctor_set(x_587, 0, x_580);
lean_ctor_set(x_587, 1, x_584);
if (lean_is_scalar(x_22)) {
 x_588 = lean_alloc_ctor(1, 1, 0);
} else {
 x_588 = x_22;
}
lean_ctor_set(x_588, 0, x_587);
if (lean_is_scalar(x_586)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_586;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_585);
return x_589;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_580);
lean_dec(x_564);
lean_dec(x_22);
x_590 = lean_ctor_get(x_583, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_583, 1);
lean_inc(x_591);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_592 = x_583;
} else {
 lean_dec_ref(x_583);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_590);
lean_ctor_set(x_593, 1, x_591);
return x_593;
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
lean_dec(x_564);
lean_dec(x_399);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_594 = lean_ctor_get(x_579, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_579, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 lean_ctor_release(x_579, 1);
 x_596 = x_579;
} else {
 lean_dec_ref(x_579);
 x_596 = lean_box(0);
}
if (lean_is_scalar(x_596)) {
 x_597 = lean_alloc_ctor(1, 2, 0);
} else {
 x_597 = x_596;
}
lean_ctor_set(x_597, 0, x_594);
lean_ctor_set(x_597, 1, x_595);
return x_597;
}
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_562);
x_639 = lean_box(0);
x_640 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_641 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_642 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_640, x_399, x_641, x_6, x_7, x_8, x_9, x_563);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_642, 1);
lean_inc(x_644);
lean_dec(x_642);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_645 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_643, x_6, x_7, x_8, x_9, x_644);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; 
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
x_649 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_649 == 0)
{
lean_object* x_662; 
lean_dec(x_27);
lean_dec(x_23);
x_662 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_648, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_647);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; lean_object* x_664; 
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
lean_dec(x_662);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_664 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_650 = x_665;
x_651 = x_666;
goto block_661;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_646);
lean_dec(x_564);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_667 = lean_ctor_get(x_664, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_664, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_669 = x_664;
} else {
 lean_dec_ref(x_664);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
return x_670;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_646);
lean_dec(x_564);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_671 = lean_ctor_get(x_662, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_662, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 x_673 = x_662;
} else {
 lean_dec_ref(x_662);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_675 = lean_array_get_size(x_23);
x_676 = l_Array_toSubarray___rarg(x_23, x_27, x_675);
x_677 = l_Array_ofSubarray___rarg(x_676);
lean_dec(x_676);
x_678 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_678, 0, x_648);
lean_ctor_set(x_678, 1, x_677);
x_679 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_680 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_678, x_679, x_6, x_7, x_8, x_9, x_647);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_ctor_get(x_681, 0);
lean_inc(x_683);
x_684 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_683, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_682);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
lean_dec(x_684);
x_686 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_686, 0, x_681);
lean_ctor_set(x_686, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_687 = l_Lean_Compiler_LCNF_Simp_simp(x_686, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_685);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_650 = x_688;
x_651 = x_689;
goto block_661;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_646);
lean_dec(x_564);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_690 = lean_ctor_get(x_687, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_687, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_692 = x_687;
} else {
 lean_dec_ref(x_687);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_681);
lean_dec(x_646);
lean_dec(x_564);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_694 = lean_ctor_get(x_684, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_684, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_696 = x_684;
} else {
 lean_dec_ref(x_684);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_694);
lean_ctor_set(x_697, 1, x_695);
return x_697;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_646);
lean_dec(x_564);
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
x_698 = lean_ctor_get(x_680, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_680, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_700 = x_680;
} else {
 lean_dec_ref(x_680);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
block_661:
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_646);
if (lean_is_scalar(x_564)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_564;
 lean_ctor_set_tag(x_653, 1);
}
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_639);
x_654 = lean_array_mk(x_653);
x_655 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_654, x_650, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_651);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_654);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_658 = x_655;
} else {
 lean_dec_ref(x_655);
 x_658 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_659 = lean_alloc_ctor(1, 1, 0);
} else {
 x_659 = x_22;
}
lean_ctor_set(x_659, 0, x_656);
if (lean_is_scalar(x_658)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_658;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_657);
return x_660;
}
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_564);
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
x_702 = lean_ctor_get(x_645, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_645, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_645)) {
 lean_ctor_release(x_645, 0);
 lean_ctor_release(x_645, 1);
 x_704 = x_645;
} else {
 lean_dec_ref(x_645);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_702);
lean_ctor_set(x_705, 1, x_703);
return x_705;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_564);
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
x_706 = lean_ctor_get(x_642, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_642, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_708 = x_642;
} else {
 lean_dec_ref(x_642);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_33);
lean_dec(x_21);
x_710 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_400);
x_711 = lean_ctor_get(x_710, 1);
lean_inc(x_711);
lean_dec(x_710);
x_712 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_712, 0, x_3);
lean_closure_set(x_712, 1, x_4);
lean_closure_set(x_712, 2, x_5);
lean_closure_set(x_712, 3, x_27);
lean_closure_set(x_712, 4, x_24);
lean_closure_set(x_712, 5, x_26);
lean_closure_set(x_712, 6, x_2);
lean_closure_set(x_712, 7, x_23);
x_713 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_399, x_712, x_6, x_7, x_8, x_9, x_711);
if (lean_obj_tag(x_713) == 0)
{
uint8_t x_714; 
x_714 = !lean_is_exclusive(x_713);
if (x_714 == 0)
{
lean_object* x_715; lean_object* x_716; 
x_715 = lean_ctor_get(x_713, 0);
if (lean_is_scalar(x_22)) {
 x_716 = lean_alloc_ctor(1, 1, 0);
} else {
 x_716 = x_22;
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_713, 0, x_716);
return x_713;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_717 = lean_ctor_get(x_713, 0);
x_718 = lean_ctor_get(x_713, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_713);
if (lean_is_scalar(x_22)) {
 x_719 = lean_alloc_ctor(1, 1, 0);
} else {
 x_719 = x_22;
}
lean_ctor_set(x_719, 0, x_717);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_718);
return x_720;
}
}
else
{
uint8_t x_721; 
lean_dec(x_22);
x_721 = !lean_is_exclusive(x_713);
if (x_721 == 0)
{
return x_713;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_713, 0);
x_723 = lean_ctor_get(x_713, 1);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_713);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
}
else
{
uint8_t x_725; 
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
x_725 = !lean_is_exclusive(x_398);
if (x_725 == 0)
{
return x_398;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_398, 0);
x_727 = lean_ctor_get(x_398, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_398);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
}
else
{
uint8_t x_748; 
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
x_748 = !lean_is_exclusive(x_394);
if (x_748 == 0)
{
return x_394;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_394, 0);
x_750 = lean_ctor_get(x_394, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_394);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
case 2:
{
uint8_t x_752; lean_object* x_753; 
lean_dec(x_11);
x_752 = 0;
lean_inc(x_33);
x_753 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_752, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; uint8_t x_1089; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
x_1089 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1089 == 0)
{
lean_object* x_1090; 
x_1090 = lean_box(0);
x_756 = x_1090;
goto block_1088;
}
else
{
uint8_t x_1091; 
x_1091 = lean_nat_dec_eq(x_24, x_27);
if (x_1091 == 0)
{
lean_object* x_1092; 
x_1092 = lean_box(0);
x_756 = x_1092;
goto block_1088;
}
else
{
lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1093 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_755);
x_1094 = lean_ctor_get(x_1093, 1);
lean_inc(x_1094);
lean_dec(x_1093);
x_1095 = l_Lean_Compiler_LCNF_Simp_simp(x_754, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1094);
if (lean_obj_tag(x_1095) == 0)
{
uint8_t x_1096; 
x_1096 = !lean_is_exclusive(x_1095);
if (x_1096 == 0)
{
lean_object* x_1097; lean_object* x_1098; 
x_1097 = lean_ctor_get(x_1095, 0);
x_1098 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1098, 0, x_1097);
lean_ctor_set(x_1095, 0, x_1098);
return x_1095;
}
else
{
lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1099 = lean_ctor_get(x_1095, 0);
x_1100 = lean_ctor_get(x_1095, 1);
lean_inc(x_1100);
lean_inc(x_1099);
lean_dec(x_1095);
x_1101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1101, 0, x_1099);
x_1102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1100);
return x_1102;
}
}
else
{
uint8_t x_1103; 
x_1103 = !lean_is_exclusive(x_1095);
if (x_1103 == 0)
{
return x_1095;
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; 
x_1104 = lean_ctor_get(x_1095, 0);
x_1105 = lean_ctor_get(x_1095, 1);
lean_inc(x_1105);
lean_inc(x_1104);
lean_dec(x_1095);
x_1106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1106, 0, x_1104);
lean_ctor_set(x_1106, 1, x_1105);
return x_1106;
}
}
}
}
block_1088:
{
lean_object* x_757; 
lean_dec(x_756);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_757 = l_Lean_Compiler_LCNF_Simp_simp(x_754, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_755);
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_758; lean_object* x_759; uint8_t x_760; 
x_758 = lean_ctor_get(x_757, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_757, 1);
lean_inc(x_759);
lean_dec(x_757);
lean_inc(x_758);
x_760 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_758);
if (x_760 == 0)
{
lean_object* x_761; uint8_t x_762; 
x_761 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_759);
x_762 = !lean_is_exclusive(x_761);
if (x_762 == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; uint8_t x_771; 
x_763 = lean_ctor_get(x_761, 1);
x_764 = lean_ctor_get(x_761, 0);
lean_dec(x_764);
x_765 = lean_ctor_get(x_21, 2);
lean_inc(x_765);
lean_dec(x_21);
x_766 = l_Lean_Compiler_LCNF_inferAppType(x_765, x_33, x_6, x_7, x_8, x_9, x_763);
x_767 = lean_ctor_get(x_766, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_766, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 x_769 = x_766;
} else {
 lean_dec_ref(x_766);
 x_769 = lean_box(0);
}
lean_inc(x_767);
x_770 = l_Lean_Expr_headBeta(x_767);
x_771 = l_Lean_Expr_isForall(x_770);
lean_dec(x_770);
if (x_771 == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint8_t x_777; lean_object* x_778; lean_object* x_779; 
x_772 = l_Lean_Compiler_LCNF_mkAuxParam(x_767, x_752, x_6, x_7, x_8, x_9, x_768);
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_772, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_775 = x_772;
} else {
 lean_dec_ref(x_772);
 x_775 = lean_box(0);
}
x_776 = lean_ctor_get(x_773, 0);
lean_inc(x_776);
x_777 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_777 == 0)
{
lean_object* x_807; 
lean_free_object(x_761);
lean_dec(x_27);
lean_dec(x_23);
x_807 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_776, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_774);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; 
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
lean_dec(x_807);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_809 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_808);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
x_778 = x_810;
x_779 = x_811;
goto block_806;
}
else
{
uint8_t x_812; 
lean_dec(x_775);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_812 = !lean_is_exclusive(x_809);
if (x_812 == 0)
{
return x_809;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_809, 0);
x_814 = lean_ctor_get(x_809, 1);
lean_inc(x_814);
lean_inc(x_813);
lean_dec(x_809);
x_815 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
return x_815;
}
}
}
else
{
uint8_t x_816; 
lean_dec(x_775);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_816 = !lean_is_exclusive(x_807);
if (x_816 == 0)
{
return x_807;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_807, 0);
x_818 = lean_ctor_get(x_807, 1);
lean_inc(x_818);
lean_inc(x_817);
lean_dec(x_807);
x_819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_819, 0, x_817);
lean_ctor_set(x_819, 1, x_818);
return x_819;
}
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_820 = lean_array_get_size(x_23);
x_821 = l_Array_toSubarray___rarg(x_23, x_27, x_820);
x_822 = l_Array_ofSubarray___rarg(x_821);
lean_dec(x_821);
lean_ctor_set_tag(x_761, 4);
lean_ctor_set(x_761, 1, x_822);
lean_ctor_set(x_761, 0, x_776);
x_823 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_824 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_761, x_823, x_6, x_7, x_8, x_9, x_774);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_827 = lean_ctor_get(x_825, 0);
lean_inc(x_827);
x_828 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_827, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_826);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; 
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec(x_828);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_825);
lean_ctor_set(x_830, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_831 = l_Lean_Compiler_LCNF_Simp_simp(x_830, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_829);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_831, 1);
lean_inc(x_833);
lean_dec(x_831);
x_778 = x_832;
x_779 = x_833;
goto block_806;
}
else
{
uint8_t x_834; 
lean_dec(x_775);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_834 = !lean_is_exclusive(x_831);
if (x_834 == 0)
{
return x_831;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_835 = lean_ctor_get(x_831, 0);
x_836 = lean_ctor_get(x_831, 1);
lean_inc(x_836);
lean_inc(x_835);
lean_dec(x_831);
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_835);
lean_ctor_set(x_837, 1, x_836);
return x_837;
}
}
}
else
{
uint8_t x_838; 
lean_dec(x_825);
lean_dec(x_775);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_838 = !lean_is_exclusive(x_828);
if (x_838 == 0)
{
return x_828;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_828, 0);
x_840 = lean_ctor_get(x_828, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_828);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
else
{
uint8_t x_842; 
lean_dec(x_775);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_758);
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
x_842 = !lean_is_exclusive(x_824);
if (x_842 == 0)
{
return x_824;
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_843 = lean_ctor_get(x_824, 0);
x_844 = lean_ctor_get(x_824, 1);
lean_inc(x_844);
lean_inc(x_843);
lean_dec(x_824);
x_845 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_844);
return x_845;
}
}
}
block_806:
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_780 = lean_box(0);
if (lean_is_scalar(x_775)) {
 x_781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_781 = x_775;
 lean_ctor_set_tag(x_781, 1);
}
lean_ctor_set(x_781, 0, x_773);
lean_ctor_set(x_781, 1, x_780);
x_782 = lean_array_mk(x_781);
x_783 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_784 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_782, x_778, x_783, x_6, x_7, x_8, x_9, x_779);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
lean_inc(x_785);
x_787 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_787, 0, x_785);
lean_closure_set(x_787, 1, x_780);
x_788 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_758, x_787, x_6, x_7, x_8, x_9, x_786);
if (lean_obj_tag(x_788) == 0)
{
uint8_t x_789; 
x_789 = !lean_is_exclusive(x_788);
if (x_789 == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_788, 0);
if (lean_is_scalar(x_769)) {
 x_791 = lean_alloc_ctor(2, 2, 0);
} else {
 x_791 = x_769;
 lean_ctor_set_tag(x_791, 2);
}
lean_ctor_set(x_791, 0, x_785);
lean_ctor_set(x_791, 1, x_790);
if (lean_is_scalar(x_22)) {
 x_792 = lean_alloc_ctor(1, 1, 0);
} else {
 x_792 = x_22;
}
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_788, 0, x_792);
return x_788;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_793 = lean_ctor_get(x_788, 0);
x_794 = lean_ctor_get(x_788, 1);
lean_inc(x_794);
lean_inc(x_793);
lean_dec(x_788);
if (lean_is_scalar(x_769)) {
 x_795 = lean_alloc_ctor(2, 2, 0);
} else {
 x_795 = x_769;
 lean_ctor_set_tag(x_795, 2);
}
lean_ctor_set(x_795, 0, x_785);
lean_ctor_set(x_795, 1, x_793);
if (lean_is_scalar(x_22)) {
 x_796 = lean_alloc_ctor(1, 1, 0);
} else {
 x_796 = x_22;
}
lean_ctor_set(x_796, 0, x_795);
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_794);
return x_797;
}
}
else
{
uint8_t x_798; 
lean_dec(x_785);
lean_dec(x_769);
lean_dec(x_22);
x_798 = !lean_is_exclusive(x_788);
if (x_798 == 0)
{
return x_788;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_788, 0);
x_800 = lean_ctor_get(x_788, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_788);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
}
}
}
else
{
uint8_t x_802; 
lean_dec(x_769);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_802 = !lean_is_exclusive(x_784);
if (x_802 == 0)
{
return x_784;
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_803 = lean_ctor_get(x_784, 0);
x_804 = lean_ctor_get(x_784, 1);
lean_inc(x_804);
lean_inc(x_803);
lean_dec(x_784);
x_805 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_805, 0, x_803);
lean_ctor_set(x_805, 1, x_804);
return x_805;
}
}
}
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_767);
x_846 = lean_box(0);
x_847 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_848 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_849 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_847, x_758, x_848, x_6, x_7, x_8, x_9, x_768);
if (lean_obj_tag(x_849) == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec(x_849);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_852 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_850, x_6, x_7, x_8, x_9, x_851);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; lean_object* x_857; lean_object* x_858; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
x_855 = lean_ctor_get(x_853, 0);
lean_inc(x_855);
x_856 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_856 == 0)
{
lean_object* x_871; 
lean_free_object(x_761);
lean_dec(x_27);
lean_dec(x_23);
x_871 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_855, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_854);
if (lean_obj_tag(x_871) == 0)
{
lean_object* x_872; lean_object* x_873; 
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
lean_dec(x_871);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_873 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_872);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; 
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
x_857 = x_874;
x_858 = x_875;
goto block_870;
}
else
{
uint8_t x_876; 
lean_dec(x_853);
lean_dec(x_769);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_876 = !lean_is_exclusive(x_873);
if (x_876 == 0)
{
return x_873;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_873, 0);
x_878 = lean_ctor_get(x_873, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_873);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
else
{
uint8_t x_880; 
lean_dec(x_853);
lean_dec(x_769);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_880 = !lean_is_exclusive(x_871);
if (x_880 == 0)
{
return x_871;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_871, 0);
x_882 = lean_ctor_get(x_871, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_871);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_884 = lean_array_get_size(x_23);
x_885 = l_Array_toSubarray___rarg(x_23, x_27, x_884);
x_886 = l_Array_ofSubarray___rarg(x_885);
lean_dec(x_885);
lean_ctor_set_tag(x_761, 4);
lean_ctor_set(x_761, 1, x_886);
lean_ctor_set(x_761, 0, x_855);
x_887 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_888 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_761, x_887, x_6, x_7, x_8, x_9, x_854);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_888, 1);
lean_inc(x_890);
lean_dec(x_888);
x_891 = lean_ctor_get(x_889, 0);
lean_inc(x_891);
x_892 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_891, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_890);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
lean_dec(x_892);
x_894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_894, 0, x_889);
lean_ctor_set(x_894, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_895 = l_Lean_Compiler_LCNF_Simp_simp(x_894, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_893);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; 
x_896 = lean_ctor_get(x_895, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_895, 1);
lean_inc(x_897);
lean_dec(x_895);
x_857 = x_896;
x_858 = x_897;
goto block_870;
}
else
{
uint8_t x_898; 
lean_dec(x_853);
lean_dec(x_769);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_898 = !lean_is_exclusive(x_895);
if (x_898 == 0)
{
return x_895;
}
else
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; 
x_899 = lean_ctor_get(x_895, 0);
x_900 = lean_ctor_get(x_895, 1);
lean_inc(x_900);
lean_inc(x_899);
lean_dec(x_895);
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_900);
return x_901;
}
}
}
else
{
uint8_t x_902; 
lean_dec(x_889);
lean_dec(x_853);
lean_dec(x_769);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_902 = !lean_is_exclusive(x_892);
if (x_902 == 0)
{
return x_892;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_903 = lean_ctor_get(x_892, 0);
x_904 = lean_ctor_get(x_892, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_892);
x_905 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_905, 0, x_903);
lean_ctor_set(x_905, 1, x_904);
return x_905;
}
}
}
else
{
uint8_t x_906; 
lean_dec(x_853);
lean_dec(x_769);
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
x_906 = !lean_is_exclusive(x_888);
if (x_906 == 0)
{
return x_888;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
x_907 = lean_ctor_get(x_888, 0);
x_908 = lean_ctor_get(x_888, 1);
lean_inc(x_908);
lean_inc(x_907);
lean_dec(x_888);
x_909 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_909, 0, x_907);
lean_ctor_set(x_909, 1, x_908);
return x_909;
}
}
}
block_870:
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; uint8_t x_863; 
x_859 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_859, 0, x_853);
if (lean_is_scalar(x_769)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_769;
 lean_ctor_set_tag(x_860, 1);
}
lean_ctor_set(x_860, 0, x_859);
lean_ctor_set(x_860, 1, x_846);
x_861 = lean_array_mk(x_860);
x_862 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_861, x_857, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_858);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_861);
x_863 = !lean_is_exclusive(x_862);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; 
x_864 = lean_ctor_get(x_862, 0);
if (lean_is_scalar(x_22)) {
 x_865 = lean_alloc_ctor(1, 1, 0);
} else {
 x_865 = x_22;
}
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_862, 0, x_865);
return x_862;
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_866 = lean_ctor_get(x_862, 0);
x_867 = lean_ctor_get(x_862, 1);
lean_inc(x_867);
lean_inc(x_866);
lean_dec(x_862);
if (lean_is_scalar(x_22)) {
 x_868 = lean_alloc_ctor(1, 1, 0);
} else {
 x_868 = x_22;
}
lean_ctor_set(x_868, 0, x_866);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_868);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
}
else
{
uint8_t x_910; 
lean_dec(x_769);
lean_free_object(x_761);
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
x_910 = !lean_is_exclusive(x_852);
if (x_910 == 0)
{
return x_852;
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
x_911 = lean_ctor_get(x_852, 0);
x_912 = lean_ctor_get(x_852, 1);
lean_inc(x_912);
lean_inc(x_911);
lean_dec(x_852);
x_913 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
}
else
{
uint8_t x_914; 
lean_dec(x_769);
lean_free_object(x_761);
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
x_914 = !lean_is_exclusive(x_849);
if (x_914 == 0)
{
return x_849;
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_849, 0);
x_916 = lean_ctor_get(x_849, 1);
lean_inc(x_916);
lean_inc(x_915);
lean_dec(x_849);
x_917 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_917, 0, x_915);
lean_ctor_set(x_917, 1, x_916);
return x_917;
}
}
}
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_918 = lean_ctor_get(x_761, 1);
lean_inc(x_918);
lean_dec(x_761);
x_919 = lean_ctor_get(x_21, 2);
lean_inc(x_919);
lean_dec(x_21);
x_920 = l_Lean_Compiler_LCNF_inferAppType(x_919, x_33, x_6, x_7, x_8, x_9, x_918);
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_923 = x_920;
} else {
 lean_dec_ref(x_920);
 x_923 = lean_box(0);
}
lean_inc(x_921);
x_924 = l_Lean_Expr_headBeta(x_921);
x_925 = l_Lean_Expr_isForall(x_924);
lean_dec(x_924);
if (x_925 == 0)
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; uint8_t x_931; lean_object* x_932; lean_object* x_933; 
x_926 = l_Lean_Compiler_LCNF_mkAuxParam(x_921, x_752, x_6, x_7, x_8, x_9, x_922);
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_929 = x_926;
} else {
 lean_dec_ref(x_926);
 x_929 = lean_box(0);
}
x_930 = lean_ctor_get(x_927, 0);
lean_inc(x_930);
x_931 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_931 == 0)
{
lean_object* x_958; 
lean_dec(x_27);
lean_dec(x_23);
x_958 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_930, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_928);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; 
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec(x_958);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_960 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_959);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; 
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec(x_960);
x_932 = x_961;
x_933 = x_962;
goto block_957;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_929);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_963 = lean_ctor_get(x_960, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_960, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_965 = x_960;
} else {
 lean_dec_ref(x_960);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_965)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_965;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
return x_966;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_929);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_967 = lean_ctor_get(x_958, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_958, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_969 = x_958;
} else {
 lean_dec_ref(x_958);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_971 = lean_array_get_size(x_23);
x_972 = l_Array_toSubarray___rarg(x_23, x_27, x_971);
x_973 = l_Array_ofSubarray___rarg(x_972);
lean_dec(x_972);
x_974 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_974, 0, x_930);
lean_ctor_set(x_974, 1, x_973);
x_975 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_976 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_974, x_975, x_6, x_7, x_8, x_9, x_928);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
lean_dec(x_976);
x_979 = lean_ctor_get(x_977, 0);
lean_inc(x_979);
x_980 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_979, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_978);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_980, 1);
lean_inc(x_981);
lean_dec(x_980);
x_982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_982, 0, x_977);
lean_ctor_set(x_982, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_983 = l_Lean_Compiler_LCNF_Simp_simp(x_982, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_981);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; 
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
lean_dec(x_983);
x_932 = x_984;
x_933 = x_985;
goto block_957;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_929);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_986 = lean_ctor_get(x_983, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_983, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_988 = x_983;
} else {
 lean_dec_ref(x_983);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
else
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
lean_dec(x_977);
lean_dec(x_929);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_990 = lean_ctor_get(x_980, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_980, 1);
lean_inc(x_991);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_992 = x_980;
} else {
 lean_dec_ref(x_980);
 x_992 = lean_box(0);
}
if (lean_is_scalar(x_992)) {
 x_993 = lean_alloc_ctor(1, 2, 0);
} else {
 x_993 = x_992;
}
lean_ctor_set(x_993, 0, x_990);
lean_ctor_set(x_993, 1, x_991);
return x_993;
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; 
lean_dec(x_929);
lean_dec(x_927);
lean_dec(x_923);
lean_dec(x_758);
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
x_994 = lean_ctor_get(x_976, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_976, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_996 = x_976;
} else {
 lean_dec_ref(x_976);
 x_996 = lean_box(0);
}
if (lean_is_scalar(x_996)) {
 x_997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_997 = x_996;
}
lean_ctor_set(x_997, 0, x_994);
lean_ctor_set(x_997, 1, x_995);
return x_997;
}
}
block_957:
{
lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_934 = lean_box(0);
if (lean_is_scalar(x_929)) {
 x_935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_935 = x_929;
 lean_ctor_set_tag(x_935, 1);
}
lean_ctor_set(x_935, 0, x_927);
lean_ctor_set(x_935, 1, x_934);
x_936 = lean_array_mk(x_935);
x_937 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_938 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_936, x_932, x_937, x_6, x_7, x_8, x_9, x_933);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
lean_inc(x_939);
x_941 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_941, 0, x_939);
lean_closure_set(x_941, 1, x_934);
x_942 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_758, x_941, x_6, x_7, x_8, x_9, x_940);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_943 = lean_ctor_get(x_942, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_942, 1);
lean_inc(x_944);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_945 = x_942;
} else {
 lean_dec_ref(x_942);
 x_945 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_946 = lean_alloc_ctor(2, 2, 0);
} else {
 x_946 = x_923;
 lean_ctor_set_tag(x_946, 2);
}
lean_ctor_set(x_946, 0, x_939);
lean_ctor_set(x_946, 1, x_943);
if (lean_is_scalar(x_22)) {
 x_947 = lean_alloc_ctor(1, 1, 0);
} else {
 x_947 = x_22;
}
lean_ctor_set(x_947, 0, x_946);
if (lean_is_scalar(x_945)) {
 x_948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_948 = x_945;
}
lean_ctor_set(x_948, 0, x_947);
lean_ctor_set(x_948, 1, x_944);
return x_948;
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_939);
lean_dec(x_923);
lean_dec(x_22);
x_949 = lean_ctor_get(x_942, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_942, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_951 = x_942;
} else {
 lean_dec_ref(x_942);
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
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_923);
lean_dec(x_758);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_953 = lean_ctor_get(x_938, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_938, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_938)) {
 lean_ctor_release(x_938, 0);
 lean_ctor_release(x_938, 1);
 x_955 = x_938;
} else {
 lean_dec_ref(x_938);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_955)) {
 x_956 = lean_alloc_ctor(1, 2, 0);
} else {
 x_956 = x_955;
}
lean_ctor_set(x_956, 0, x_953);
lean_ctor_set(x_956, 1, x_954);
return x_956;
}
}
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_921);
x_998 = lean_box(0);
x_999 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1000 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1001 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_999, x_758, x_1000, x_6, x_7, x_8, x_9, x_922);
if (lean_obj_tag(x_1001) == 0)
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; 
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_1001, 1);
lean_inc(x_1003);
lean_dec(x_1001);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1004 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1002, x_6, x_7, x_8, x_9, x_1003);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; uint8_t x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec(x_1004);
x_1007 = lean_ctor_get(x_1005, 0);
lean_inc(x_1007);
x_1008 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1008 == 0)
{
lean_object* x_1021; 
lean_dec(x_27);
lean_dec(x_23);
x_1021 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1007, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1006);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; 
x_1022 = lean_ctor_get(x_1021, 1);
lean_inc(x_1022);
lean_dec(x_1021);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1023 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1022);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; lean_object* x_1025; 
x_1024 = lean_ctor_get(x_1023, 0);
lean_inc(x_1024);
x_1025 = lean_ctor_get(x_1023, 1);
lean_inc(x_1025);
lean_dec(x_1023);
x_1009 = x_1024;
x_1010 = x_1025;
goto block_1020;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_1005);
lean_dec(x_923);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1026 = lean_ctor_get(x_1023, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1023, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1023)) {
 lean_ctor_release(x_1023, 0);
 lean_ctor_release(x_1023, 1);
 x_1028 = x_1023;
} else {
 lean_dec_ref(x_1023);
 x_1028 = lean_box(0);
}
if (lean_is_scalar(x_1028)) {
 x_1029 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1029 = x_1028;
}
lean_ctor_set(x_1029, 0, x_1026);
lean_ctor_set(x_1029, 1, x_1027);
return x_1029;
}
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_1005);
lean_dec(x_923);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1030 = lean_ctor_get(x_1021, 0);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1021, 1);
lean_inc(x_1031);
if (lean_is_exclusive(x_1021)) {
 lean_ctor_release(x_1021, 0);
 lean_ctor_release(x_1021, 1);
 x_1032 = x_1021;
} else {
 lean_dec_ref(x_1021);
 x_1032 = lean_box(0);
}
if (lean_is_scalar(x_1032)) {
 x_1033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1033 = x_1032;
}
lean_ctor_set(x_1033, 0, x_1030);
lean_ctor_set(x_1033, 1, x_1031);
return x_1033;
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; 
x_1034 = lean_array_get_size(x_23);
x_1035 = l_Array_toSubarray___rarg(x_23, x_27, x_1034);
x_1036 = l_Array_ofSubarray___rarg(x_1035);
lean_dec(x_1035);
x_1037 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1037, 0, x_1007);
lean_ctor_set(x_1037, 1, x_1036);
x_1038 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1039 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1037, x_1038, x_6, x_7, x_8, x_9, x_1006);
if (lean_obj_tag(x_1039) == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1040 = lean_ctor_get(x_1039, 0);
lean_inc(x_1040);
x_1041 = lean_ctor_get(x_1039, 1);
lean_inc(x_1041);
lean_dec(x_1039);
x_1042 = lean_ctor_get(x_1040, 0);
lean_inc(x_1042);
x_1043 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1042, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1041);
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; 
x_1044 = lean_ctor_get(x_1043, 1);
lean_inc(x_1044);
lean_dec(x_1043);
x_1045 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1045, 0, x_1040);
lean_ctor_set(x_1045, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1046 = l_Lean_Compiler_LCNF_Simp_simp(x_1045, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1044);
if (lean_obj_tag(x_1046) == 0)
{
lean_object* x_1047; lean_object* x_1048; 
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1009 = x_1047;
x_1010 = x_1048;
goto block_1020;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1005);
lean_dec(x_923);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1049 = lean_ctor_get(x_1046, 0);
lean_inc(x_1049);
x_1050 = lean_ctor_get(x_1046, 1);
lean_inc(x_1050);
if (lean_is_exclusive(x_1046)) {
 lean_ctor_release(x_1046, 0);
 lean_ctor_release(x_1046, 1);
 x_1051 = x_1046;
} else {
 lean_dec_ref(x_1046);
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
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1040);
lean_dec(x_1005);
lean_dec(x_923);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1053 = lean_ctor_get(x_1043, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1043, 1);
lean_inc(x_1054);
if (lean_is_exclusive(x_1043)) {
 lean_ctor_release(x_1043, 0);
 lean_ctor_release(x_1043, 1);
 x_1055 = x_1043;
} else {
 lean_dec_ref(x_1043);
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
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1005);
lean_dec(x_923);
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
x_1057 = lean_ctor_get(x_1039, 0);
lean_inc(x_1057);
x_1058 = lean_ctor_get(x_1039, 1);
lean_inc(x_1058);
if (lean_is_exclusive(x_1039)) {
 lean_ctor_release(x_1039, 0);
 lean_ctor_release(x_1039, 1);
 x_1059 = x_1039;
} else {
 lean_dec_ref(x_1039);
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
block_1020:
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1011 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1011, 0, x_1005);
if (lean_is_scalar(x_923)) {
 x_1012 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1012 = x_923;
 lean_ctor_set_tag(x_1012, 1);
}
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_998);
x_1013 = lean_array_mk(x_1012);
x_1014 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1013, x_1009, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1010);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1013);
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
if (lean_is_scalar(x_22)) {
 x_1018 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1018 = x_22;
}
lean_ctor_set(x_1018, 0, x_1015);
if (lean_is_scalar(x_1017)) {
 x_1019 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1019 = x_1017;
}
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_1016);
return x_1019;
}
}
else
{
lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
lean_dec(x_923);
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
x_1061 = lean_ctor_get(x_1004, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1004, 1);
lean_inc(x_1062);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1063 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1063 = lean_box(0);
}
if (lean_is_scalar(x_1063)) {
 x_1064 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1064 = x_1063;
}
lean_ctor_set(x_1064, 0, x_1061);
lean_ctor_set(x_1064, 1, x_1062);
return x_1064;
}
}
else
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_923);
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
x_1065 = lean_ctor_get(x_1001, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_1001, 1);
lean_inc(x_1066);
if (lean_is_exclusive(x_1001)) {
 lean_ctor_release(x_1001, 0);
 lean_ctor_release(x_1001, 1);
 x_1067 = x_1001;
} else {
 lean_dec_ref(x_1001);
 x_1067 = lean_box(0);
}
if (lean_is_scalar(x_1067)) {
 x_1068 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1068 = x_1067;
}
lean_ctor_set(x_1068, 0, x_1065);
lean_ctor_set(x_1068, 1, x_1066);
return x_1068;
}
}
}
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_33);
lean_dec(x_21);
x_1069 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_759);
x_1070 = lean_ctor_get(x_1069, 1);
lean_inc(x_1070);
lean_dec(x_1069);
x_1071 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_1071, 0, x_3);
lean_closure_set(x_1071, 1, x_4);
lean_closure_set(x_1071, 2, x_5);
lean_closure_set(x_1071, 3, x_27);
lean_closure_set(x_1071, 4, x_24);
lean_closure_set(x_1071, 5, x_26);
lean_closure_set(x_1071, 6, x_2);
lean_closure_set(x_1071, 7, x_23);
x_1072 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_758, x_1071, x_6, x_7, x_8, x_9, x_1070);
if (lean_obj_tag(x_1072) == 0)
{
uint8_t x_1073; 
x_1073 = !lean_is_exclusive(x_1072);
if (x_1073 == 0)
{
lean_object* x_1074; lean_object* x_1075; 
x_1074 = lean_ctor_get(x_1072, 0);
if (lean_is_scalar(x_22)) {
 x_1075 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1075 = x_22;
}
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1072, 0, x_1075);
return x_1072;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1076 = lean_ctor_get(x_1072, 0);
x_1077 = lean_ctor_get(x_1072, 1);
lean_inc(x_1077);
lean_inc(x_1076);
lean_dec(x_1072);
if (lean_is_scalar(x_22)) {
 x_1078 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1078 = x_22;
}
lean_ctor_set(x_1078, 0, x_1076);
x_1079 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1079, 0, x_1078);
lean_ctor_set(x_1079, 1, x_1077);
return x_1079;
}
}
else
{
uint8_t x_1080; 
lean_dec(x_22);
x_1080 = !lean_is_exclusive(x_1072);
if (x_1080 == 0)
{
return x_1072;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1072, 0);
x_1082 = lean_ctor_get(x_1072, 1);
lean_inc(x_1082);
lean_inc(x_1081);
lean_dec(x_1072);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1082);
return x_1083;
}
}
}
}
else
{
uint8_t x_1084; 
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
x_1084 = !lean_is_exclusive(x_757);
if (x_1084 == 0)
{
return x_757;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1085 = lean_ctor_get(x_757, 0);
x_1086 = lean_ctor_get(x_757, 1);
lean_inc(x_1086);
lean_inc(x_1085);
lean_dec(x_757);
x_1087 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1087, 0, x_1085);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
}
}
else
{
uint8_t x_1107; 
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
x_1107 = !lean_is_exclusive(x_753);
if (x_1107 == 0)
{
return x_753;
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; 
x_1108 = lean_ctor_get(x_753, 0);
x_1109 = lean_ctor_get(x_753, 1);
lean_inc(x_1109);
lean_inc(x_1108);
lean_dec(x_753);
x_1110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1110, 0, x_1108);
lean_ctor_set(x_1110, 1, x_1109);
return x_1110;
}
}
}
case 3:
{
lean_object* x_1111; lean_object* x_1112; 
x_1111 = lean_ctor_get(x_11, 0);
lean_inc(x_1111);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_1111);
x_1112 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_1111, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_1112) == 0)
{
lean_object* x_1113; lean_object* x_1114; uint8_t x_1115; 
x_1113 = lean_ctor_get(x_1112, 0);
lean_inc(x_1113);
x_1114 = lean_ctor_get(x_1112, 1);
lean_inc(x_1114);
lean_dec(x_1112);
x_1115 = !lean_is_exclusive(x_3);
if (x_1115 == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; uint8_t x_1120; lean_object* x_1121; 
x_1116 = lean_ctor_get(x_3, 2);
x_1117 = lean_ctor_get(x_3, 3);
lean_inc(x_1111);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1111);
lean_ctor_set(x_1118, 1, x_1116);
x_1119 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_1117, x_1111, x_1113);
lean_ctor_set(x_3, 3, x_1119);
lean_ctor_set(x_3, 2, x_1118);
x_1120 = 0;
lean_inc(x_33);
x_1121 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1120, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1114);
lean_dec(x_29);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; uint8_t x_1457; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1457 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1457 == 0)
{
lean_object* x_1458; 
x_1458 = lean_box(0);
x_1124 = x_1458;
goto block_1456;
}
else
{
uint8_t x_1459; 
x_1459 = lean_nat_dec_eq(x_24, x_27);
if (x_1459 == 0)
{
lean_object* x_1460; 
x_1460 = lean_box(0);
x_1124 = x_1460;
goto block_1456;
}
else
{
lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1461 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1123);
x_1462 = lean_ctor_get(x_1461, 1);
lean_inc(x_1462);
lean_dec(x_1461);
x_1463 = l_Lean_Compiler_LCNF_Simp_simp(x_1122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1462);
if (lean_obj_tag(x_1463) == 0)
{
uint8_t x_1464; 
x_1464 = !lean_is_exclusive(x_1463);
if (x_1464 == 0)
{
lean_object* x_1465; lean_object* x_1466; 
x_1465 = lean_ctor_get(x_1463, 0);
x_1466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1466, 0, x_1465);
lean_ctor_set(x_1463, 0, x_1466);
return x_1463;
}
else
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
x_1467 = lean_ctor_get(x_1463, 0);
x_1468 = lean_ctor_get(x_1463, 1);
lean_inc(x_1468);
lean_inc(x_1467);
lean_dec(x_1463);
x_1469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1469, 0, x_1467);
x_1470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1470, 0, x_1469);
lean_ctor_set(x_1470, 1, x_1468);
return x_1470;
}
}
else
{
uint8_t x_1471; 
x_1471 = !lean_is_exclusive(x_1463);
if (x_1471 == 0)
{
return x_1463;
}
else
{
lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1472 = lean_ctor_get(x_1463, 0);
x_1473 = lean_ctor_get(x_1463, 1);
lean_inc(x_1473);
lean_inc(x_1472);
lean_dec(x_1463);
x_1474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1474, 0, x_1472);
lean_ctor_set(x_1474, 1, x_1473);
return x_1474;
}
}
}
}
block_1456:
{
lean_object* x_1125; 
lean_dec(x_1124);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1125 = l_Lean_Compiler_LCNF_Simp_simp(x_1122, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1123);
if (lean_obj_tag(x_1125) == 0)
{
lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; 
x_1126 = lean_ctor_get(x_1125, 0);
lean_inc(x_1126);
x_1127 = lean_ctor_get(x_1125, 1);
lean_inc(x_1127);
lean_dec(x_1125);
lean_inc(x_1126);
x_1128 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1126);
if (x_1128 == 0)
{
lean_object* x_1129; uint8_t x_1130; 
x_1129 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1127);
x_1130 = !lean_is_exclusive(x_1129);
if (x_1130 == 0)
{
lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; 
x_1131 = lean_ctor_get(x_1129, 1);
x_1132 = lean_ctor_get(x_1129, 0);
lean_dec(x_1132);
x_1133 = lean_ctor_get(x_21, 2);
lean_inc(x_1133);
lean_dec(x_21);
x_1134 = l_Lean_Compiler_LCNF_inferAppType(x_1133, x_33, x_6, x_7, x_8, x_9, x_1131);
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
if (lean_is_exclusive(x_1134)) {
 lean_ctor_release(x_1134, 0);
 lean_ctor_release(x_1134, 1);
 x_1137 = x_1134;
} else {
 lean_dec_ref(x_1134);
 x_1137 = lean_box(0);
}
lean_inc(x_1135);
x_1138 = l_Lean_Expr_headBeta(x_1135);
x_1139 = l_Lean_Expr_isForall(x_1138);
lean_dec(x_1138);
if (x_1139 == 0)
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; uint8_t x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1140 = l_Lean_Compiler_LCNF_mkAuxParam(x_1135, x_1120, x_6, x_7, x_8, x_9, x_1136);
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_ctor_get(x_1140, 1);
lean_inc(x_1142);
if (lean_is_exclusive(x_1140)) {
 lean_ctor_release(x_1140, 0);
 lean_ctor_release(x_1140, 1);
 x_1143 = x_1140;
} else {
 lean_dec_ref(x_1140);
 x_1143 = lean_box(0);
}
x_1144 = lean_ctor_get(x_1141, 0);
lean_inc(x_1144);
x_1145 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1145 == 0)
{
lean_object* x_1175; 
lean_free_object(x_1129);
lean_dec(x_27);
lean_dec(x_23);
x_1175 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1144, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1142);
if (lean_obj_tag(x_1175) == 0)
{
lean_object* x_1176; lean_object* x_1177; 
x_1176 = lean_ctor_get(x_1175, 1);
lean_inc(x_1176);
lean_dec(x_1175);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1177 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1176);
if (lean_obj_tag(x_1177) == 0)
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_1177, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_1177, 1);
lean_inc(x_1179);
lean_dec(x_1177);
x_1146 = x_1178;
x_1147 = x_1179;
goto block_1174;
}
else
{
uint8_t x_1180; 
lean_dec(x_1143);
lean_dec(x_1141);
lean_dec(x_1137);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1180 = !lean_is_exclusive(x_1177);
if (x_1180 == 0)
{
return x_1177;
}
else
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1181 = lean_ctor_get(x_1177, 0);
x_1182 = lean_ctor_get(x_1177, 1);
lean_inc(x_1182);
lean_inc(x_1181);
lean_dec(x_1177);
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
lean_dec(x_1143);
lean_dec(x_1141);
lean_dec(x_1137);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1184 = !lean_is_exclusive(x_1175);
if (x_1184 == 0)
{
return x_1175;
}
else
{
lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; 
x_1185 = lean_ctor_get(x_1175, 0);
x_1186 = lean_ctor_get(x_1175, 1);
lean_inc(x_1186);
lean_inc(x_1185);
lean_dec(x_1175);
x_1187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set(x_1187, 1, x_1186);
return x_1187;
}
}
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1188 = lean_array_get_size(x_23);
x_1189 = l_Array_toSubarray___rarg(x_23, x_27, x_1188);
x_1190 = l_Array_ofSubarray___rarg(x_1189);
lean_dec(x_1189);
lean_ctor_set_tag(x_1129, 4);
lean_ctor_set(x_1129, 1, x_1190);
lean_ctor_set(x_1129, 0, x_1144);
x_1191 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1192 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1129, x_1191, x_6, x_7, x_8, x_9, x_1142);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
x_1194 = lean_ctor_get(x_1192, 1);
lean_inc(x_1194);
lean_dec(x_1192);
x_1195 = lean_ctor_get(x_1193, 0);
lean_inc(x_1195);
x_1196 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1195, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1194);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_1196, 1);
lean_inc(x_1197);
lean_dec(x_1196);
x_1198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1198, 0, x_1193);
lean_ctor_set(x_1198, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1199 = l_Lean_Compiler_LCNF_Simp_simp(x_1198, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1197);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; lean_object* x_1201; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_ctor_get(x_1199, 1);
lean_inc(x_1201);
lean_dec(x_1199);
x_1146 = x_1200;
x_1147 = x_1201;
goto block_1174;
}
else
{
uint8_t x_1202; 
lean_dec(x_1143);
lean_dec(x_1141);
lean_dec(x_1137);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1202 = !lean_is_exclusive(x_1199);
if (x_1202 == 0)
{
return x_1199;
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1203 = lean_ctor_get(x_1199, 0);
x_1204 = lean_ctor_get(x_1199, 1);
lean_inc(x_1204);
lean_inc(x_1203);
lean_dec(x_1199);
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
lean_dec(x_1193);
lean_dec(x_1143);
lean_dec(x_1141);
lean_dec(x_1137);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1206 = !lean_is_exclusive(x_1196);
if (x_1206 == 0)
{
return x_1196;
}
else
{
lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; 
x_1207 = lean_ctor_get(x_1196, 0);
x_1208 = lean_ctor_get(x_1196, 1);
lean_inc(x_1208);
lean_inc(x_1207);
lean_dec(x_1196);
x_1209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1209, 0, x_1207);
lean_ctor_set(x_1209, 1, x_1208);
return x_1209;
}
}
}
else
{
uint8_t x_1210; 
lean_dec(x_1143);
lean_dec(x_1141);
lean_dec(x_1137);
lean_dec(x_1126);
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
x_1210 = !lean_is_exclusive(x_1192);
if (x_1210 == 0)
{
return x_1192;
}
else
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; 
x_1211 = lean_ctor_get(x_1192, 0);
x_1212 = lean_ctor_get(x_1192, 1);
lean_inc(x_1212);
lean_inc(x_1211);
lean_dec(x_1192);
x_1213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set(x_1213, 1, x_1212);
return x_1213;
}
}
}
block_1174:
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
x_1148 = lean_box(0);
if (lean_is_scalar(x_1143)) {
 x_1149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1149 = x_1143;
 lean_ctor_set_tag(x_1149, 1);
}
lean_ctor_set(x_1149, 0, x_1141);
lean_ctor_set(x_1149, 1, x_1148);
x_1150 = lean_array_mk(x_1149);
x_1151 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_1152 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1150, x_1146, x_1151, x_6, x_7, x_8, x_9, x_1147);
if (lean_obj_tag(x_1152) == 0)
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
x_1153 = lean_ctor_get(x_1152, 0);
lean_inc(x_1153);
x_1154 = lean_ctor_get(x_1152, 1);
lean_inc(x_1154);
lean_dec(x_1152);
lean_inc(x_1153);
x_1155 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1155, 0, x_1153);
lean_closure_set(x_1155, 1, x_1148);
x_1156 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1126, x_1155, x_6, x_7, x_8, x_9, x_1154);
if (lean_obj_tag(x_1156) == 0)
{
uint8_t x_1157; 
x_1157 = !lean_is_exclusive(x_1156);
if (x_1157 == 0)
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1158 = lean_ctor_get(x_1156, 0);
if (lean_is_scalar(x_1137)) {
 x_1159 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1159 = x_1137;
 lean_ctor_set_tag(x_1159, 2);
}
lean_ctor_set(x_1159, 0, x_1153);
lean_ctor_set(x_1159, 1, x_1158);
if (lean_is_scalar(x_22)) {
 x_1160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1160 = x_22;
}
lean_ctor_set(x_1160, 0, x_1159);
lean_ctor_set(x_1156, 0, x_1160);
return x_1156;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1161 = lean_ctor_get(x_1156, 0);
x_1162 = lean_ctor_get(x_1156, 1);
lean_inc(x_1162);
lean_inc(x_1161);
lean_dec(x_1156);
if (lean_is_scalar(x_1137)) {
 x_1163 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1163 = x_1137;
 lean_ctor_set_tag(x_1163, 2);
}
lean_ctor_set(x_1163, 0, x_1153);
lean_ctor_set(x_1163, 1, x_1161);
if (lean_is_scalar(x_22)) {
 x_1164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1164 = x_22;
}
lean_ctor_set(x_1164, 0, x_1163);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_1164);
lean_ctor_set(x_1165, 1, x_1162);
return x_1165;
}
}
else
{
uint8_t x_1166; 
lean_dec(x_1153);
lean_dec(x_1137);
lean_dec(x_22);
x_1166 = !lean_is_exclusive(x_1156);
if (x_1166 == 0)
{
return x_1156;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
x_1167 = lean_ctor_get(x_1156, 0);
x_1168 = lean_ctor_get(x_1156, 1);
lean_inc(x_1168);
lean_inc(x_1167);
lean_dec(x_1156);
x_1169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1169, 0, x_1167);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
}
else
{
uint8_t x_1170; 
lean_dec(x_1137);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1170 = !lean_is_exclusive(x_1152);
if (x_1170 == 0)
{
return x_1152;
}
else
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1171 = lean_ctor_get(x_1152, 0);
x_1172 = lean_ctor_get(x_1152, 1);
lean_inc(x_1172);
lean_inc(x_1171);
lean_dec(x_1152);
x_1173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1173, 0, x_1171);
lean_ctor_set(x_1173, 1, x_1172);
return x_1173;
}
}
}
}
else
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1135);
x_1214 = lean_box(0);
x_1215 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1216 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1217 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1215, x_1126, x_1216, x_6, x_7, x_8, x_9, x_1136);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1218 = lean_ctor_get(x_1217, 0);
lean_inc(x_1218);
x_1219 = lean_ctor_get(x_1217, 1);
lean_inc(x_1219);
lean_dec(x_1217);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1220 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1218, x_6, x_7, x_8, x_9, x_1219);
if (lean_obj_tag(x_1220) == 0)
{
lean_object* x_1221; lean_object* x_1222; lean_object* x_1223; uint8_t x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1221 = lean_ctor_get(x_1220, 0);
lean_inc(x_1221);
x_1222 = lean_ctor_get(x_1220, 1);
lean_inc(x_1222);
lean_dec(x_1220);
x_1223 = lean_ctor_get(x_1221, 0);
lean_inc(x_1223);
x_1224 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1224 == 0)
{
lean_object* x_1239; 
lean_free_object(x_1129);
lean_dec(x_27);
lean_dec(x_23);
x_1239 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1223, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1222);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; 
x_1240 = lean_ctor_get(x_1239, 1);
lean_inc(x_1240);
lean_dec(x_1239);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1241 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1240);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; lean_object* x_1243; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_ctor_get(x_1241, 1);
lean_inc(x_1243);
lean_dec(x_1241);
x_1225 = x_1242;
x_1226 = x_1243;
goto block_1238;
}
else
{
uint8_t x_1244; 
lean_dec(x_1221);
lean_dec(x_1137);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1244 = !lean_is_exclusive(x_1241);
if (x_1244 == 0)
{
return x_1241;
}
else
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; 
x_1245 = lean_ctor_get(x_1241, 0);
x_1246 = lean_ctor_get(x_1241, 1);
lean_inc(x_1246);
lean_inc(x_1245);
lean_dec(x_1241);
x_1247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
}
else
{
uint8_t x_1248; 
lean_dec(x_1221);
lean_dec(x_1137);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1248 = !lean_is_exclusive(x_1239);
if (x_1248 == 0)
{
return x_1239;
}
else
{
lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1249 = lean_ctor_get(x_1239, 0);
x_1250 = lean_ctor_get(x_1239, 1);
lean_inc(x_1250);
lean_inc(x_1249);
lean_dec(x_1239);
x_1251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1251, 0, x_1249);
lean_ctor_set(x_1251, 1, x_1250);
return x_1251;
}
}
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1252 = lean_array_get_size(x_23);
x_1253 = l_Array_toSubarray___rarg(x_23, x_27, x_1252);
x_1254 = l_Array_ofSubarray___rarg(x_1253);
lean_dec(x_1253);
lean_ctor_set_tag(x_1129, 4);
lean_ctor_set(x_1129, 1, x_1254);
lean_ctor_set(x_1129, 0, x_1223);
x_1255 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1256 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1129, x_1255, x_6, x_7, x_8, x_9, x_1222);
if (lean_obj_tag(x_1256) == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1256, 1);
lean_inc(x_1258);
lean_dec(x_1256);
x_1259 = lean_ctor_get(x_1257, 0);
lean_inc(x_1259);
x_1260 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1259, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1258);
if (lean_obj_tag(x_1260) == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
x_1261 = lean_ctor_get(x_1260, 1);
lean_inc(x_1261);
lean_dec(x_1260);
x_1262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1262, 0, x_1257);
lean_ctor_set(x_1262, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1263 = l_Lean_Compiler_LCNF_Simp_simp(x_1262, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1261);
if (lean_obj_tag(x_1263) == 0)
{
lean_object* x_1264; lean_object* x_1265; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
x_1265 = lean_ctor_get(x_1263, 1);
lean_inc(x_1265);
lean_dec(x_1263);
x_1225 = x_1264;
x_1226 = x_1265;
goto block_1238;
}
else
{
uint8_t x_1266; 
lean_dec(x_1221);
lean_dec(x_1137);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1266 = !lean_is_exclusive(x_1263);
if (x_1266 == 0)
{
return x_1263;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1267 = lean_ctor_get(x_1263, 0);
x_1268 = lean_ctor_get(x_1263, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_1263);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
return x_1269;
}
}
}
else
{
uint8_t x_1270; 
lean_dec(x_1257);
lean_dec(x_1221);
lean_dec(x_1137);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1270 = !lean_is_exclusive(x_1260);
if (x_1270 == 0)
{
return x_1260;
}
else
{
lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; 
x_1271 = lean_ctor_get(x_1260, 0);
x_1272 = lean_ctor_get(x_1260, 1);
lean_inc(x_1272);
lean_inc(x_1271);
lean_dec(x_1260);
x_1273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1273, 0, x_1271);
lean_ctor_set(x_1273, 1, x_1272);
return x_1273;
}
}
}
else
{
uint8_t x_1274; 
lean_dec(x_1221);
lean_dec(x_1137);
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
x_1274 = !lean_is_exclusive(x_1256);
if (x_1274 == 0)
{
return x_1256;
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; 
x_1275 = lean_ctor_get(x_1256, 0);
x_1276 = lean_ctor_get(x_1256, 1);
lean_inc(x_1276);
lean_inc(x_1275);
lean_dec(x_1256);
x_1277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1277, 0, x_1275);
lean_ctor_set(x_1277, 1, x_1276);
return x_1277;
}
}
}
block_1238:
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; uint8_t x_1231; 
x_1227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1227, 0, x_1221);
if (lean_is_scalar(x_1137)) {
 x_1228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1228 = x_1137;
 lean_ctor_set_tag(x_1228, 1);
}
lean_ctor_set(x_1228, 0, x_1227);
lean_ctor_set(x_1228, 1, x_1214);
x_1229 = lean_array_mk(x_1228);
x_1230 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1229, x_1225, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1226);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1229);
x_1231 = !lean_is_exclusive(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1230, 0);
if (lean_is_scalar(x_22)) {
 x_1233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1233 = x_22;
}
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1230, 0, x_1233);
return x_1230;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1234 = lean_ctor_get(x_1230, 0);
x_1235 = lean_ctor_get(x_1230, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1230);
if (lean_is_scalar(x_22)) {
 x_1236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1236 = x_22;
}
lean_ctor_set(x_1236, 0, x_1234);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_1236);
lean_ctor_set(x_1237, 1, x_1235);
return x_1237;
}
}
}
else
{
uint8_t x_1278; 
lean_dec(x_1137);
lean_free_object(x_1129);
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
x_1278 = !lean_is_exclusive(x_1220);
if (x_1278 == 0)
{
return x_1220;
}
else
{
lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; 
x_1279 = lean_ctor_get(x_1220, 0);
x_1280 = lean_ctor_get(x_1220, 1);
lean_inc(x_1280);
lean_inc(x_1279);
lean_dec(x_1220);
x_1281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1281, 0, x_1279);
lean_ctor_set(x_1281, 1, x_1280);
return x_1281;
}
}
}
else
{
uint8_t x_1282; 
lean_dec(x_1137);
lean_free_object(x_1129);
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
x_1282 = !lean_is_exclusive(x_1217);
if (x_1282 == 0)
{
return x_1217;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; 
x_1283 = lean_ctor_get(x_1217, 0);
x_1284 = lean_ctor_get(x_1217, 1);
lean_inc(x_1284);
lean_inc(x_1283);
lean_dec(x_1217);
x_1285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1285, 0, x_1283);
lean_ctor_set(x_1285, 1, x_1284);
return x_1285;
}
}
}
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; uint8_t x_1293; 
x_1286 = lean_ctor_get(x_1129, 1);
lean_inc(x_1286);
lean_dec(x_1129);
x_1287 = lean_ctor_get(x_21, 2);
lean_inc(x_1287);
lean_dec(x_21);
x_1288 = l_Lean_Compiler_LCNF_inferAppType(x_1287, x_33, x_6, x_7, x_8, x_9, x_1286);
x_1289 = lean_ctor_get(x_1288, 0);
lean_inc(x_1289);
x_1290 = lean_ctor_get(x_1288, 1);
lean_inc(x_1290);
if (lean_is_exclusive(x_1288)) {
 lean_ctor_release(x_1288, 0);
 lean_ctor_release(x_1288, 1);
 x_1291 = x_1288;
} else {
 lean_dec_ref(x_1288);
 x_1291 = lean_box(0);
}
lean_inc(x_1289);
x_1292 = l_Lean_Expr_headBeta(x_1289);
x_1293 = l_Lean_Expr_isForall(x_1292);
lean_dec(x_1292);
if (x_1293 == 0)
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1294 = l_Lean_Compiler_LCNF_mkAuxParam(x_1289, x_1120, x_6, x_7, x_8, x_9, x_1290);
x_1295 = lean_ctor_get(x_1294, 0);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_1294, 1);
lean_inc(x_1296);
if (lean_is_exclusive(x_1294)) {
 lean_ctor_release(x_1294, 0);
 lean_ctor_release(x_1294, 1);
 x_1297 = x_1294;
} else {
 lean_dec_ref(x_1294);
 x_1297 = lean_box(0);
}
x_1298 = lean_ctor_get(x_1295, 0);
lean_inc(x_1298);
x_1299 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1299 == 0)
{
lean_object* x_1326; 
lean_dec(x_27);
lean_dec(x_23);
x_1326 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1298, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1296);
if (lean_obj_tag(x_1326) == 0)
{
lean_object* x_1327; lean_object* x_1328; 
x_1327 = lean_ctor_get(x_1326, 1);
lean_inc(x_1327);
lean_dec(x_1326);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1328 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1327);
if (lean_obj_tag(x_1328) == 0)
{
lean_object* x_1329; lean_object* x_1330; 
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1300 = x_1329;
x_1301 = x_1330;
goto block_1325;
}
else
{
lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1334; 
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1291);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1331 = lean_ctor_get(x_1328, 0);
lean_inc(x_1331);
x_1332 = lean_ctor_get(x_1328, 1);
lean_inc(x_1332);
if (lean_is_exclusive(x_1328)) {
 lean_ctor_release(x_1328, 0);
 lean_ctor_release(x_1328, 1);
 x_1333 = x_1328;
} else {
 lean_dec_ref(x_1328);
 x_1333 = lean_box(0);
}
if (lean_is_scalar(x_1333)) {
 x_1334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1334 = x_1333;
}
lean_ctor_set(x_1334, 0, x_1331);
lean_ctor_set(x_1334, 1, x_1332);
return x_1334;
}
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1291);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1335 = lean_ctor_get(x_1326, 0);
lean_inc(x_1335);
x_1336 = lean_ctor_get(x_1326, 1);
lean_inc(x_1336);
if (lean_is_exclusive(x_1326)) {
 lean_ctor_release(x_1326, 0);
 lean_ctor_release(x_1326, 1);
 x_1337 = x_1326;
} else {
 lean_dec_ref(x_1326);
 x_1337 = lean_box(0);
}
if (lean_is_scalar(x_1337)) {
 x_1338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1338 = x_1337;
}
lean_ctor_set(x_1338, 0, x_1335);
lean_ctor_set(x_1338, 1, x_1336);
return x_1338;
}
}
else
{
lean_object* x_1339; lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1339 = lean_array_get_size(x_23);
x_1340 = l_Array_toSubarray___rarg(x_23, x_27, x_1339);
x_1341 = l_Array_ofSubarray___rarg(x_1340);
lean_dec(x_1340);
x_1342 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1342, 0, x_1298);
lean_ctor_set(x_1342, 1, x_1341);
x_1343 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1344 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1342, x_1343, x_6, x_7, x_8, x_9, x_1296);
if (lean_obj_tag(x_1344) == 0)
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1345 = lean_ctor_get(x_1344, 0);
lean_inc(x_1345);
x_1346 = lean_ctor_get(x_1344, 1);
lean_inc(x_1346);
lean_dec(x_1344);
x_1347 = lean_ctor_get(x_1345, 0);
lean_inc(x_1347);
x_1348 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1347, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1346);
if (lean_obj_tag(x_1348) == 0)
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1349 = lean_ctor_get(x_1348, 1);
lean_inc(x_1349);
lean_dec(x_1348);
x_1350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1350, 0, x_1345);
lean_ctor_set(x_1350, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1351 = l_Lean_Compiler_LCNF_Simp_simp(x_1350, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1349);
if (lean_obj_tag(x_1351) == 0)
{
lean_object* x_1352; lean_object* x_1353; 
x_1352 = lean_ctor_get(x_1351, 0);
lean_inc(x_1352);
x_1353 = lean_ctor_get(x_1351, 1);
lean_inc(x_1353);
lean_dec(x_1351);
x_1300 = x_1352;
x_1301 = x_1353;
goto block_1325;
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; 
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1291);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1354 = lean_ctor_get(x_1351, 0);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1351, 1);
lean_inc(x_1355);
if (lean_is_exclusive(x_1351)) {
 lean_ctor_release(x_1351, 0);
 lean_ctor_release(x_1351, 1);
 x_1356 = x_1351;
} else {
 lean_dec_ref(x_1351);
 x_1356 = lean_box(0);
}
if (lean_is_scalar(x_1356)) {
 x_1357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1357 = x_1356;
}
lean_ctor_set(x_1357, 0, x_1354);
lean_ctor_set(x_1357, 1, x_1355);
return x_1357;
}
}
else
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
lean_dec(x_1345);
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1291);
lean_dec(x_1126);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1358 = lean_ctor_get(x_1348, 0);
lean_inc(x_1358);
x_1359 = lean_ctor_get(x_1348, 1);
lean_inc(x_1359);
if (lean_is_exclusive(x_1348)) {
 lean_ctor_release(x_1348, 0);
 lean_ctor_release(x_1348, 1);
 x_1360 = x_1348;
} else {
 lean_dec_ref(x_1348);
 x_1360 = lean_box(0);
}
if (lean_is_scalar(x_1360)) {
 x_1361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1361 = x_1360;
}
lean_ctor_set(x_1361, 0, x_1358);
lean_ctor_set(x_1361, 1, x_1359);
return x_1361;
}
}
else
{
lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; 
lean_dec(x_1297);
lean_dec(x_1295);
lean_dec(x_1291);
lean_dec(x_1126);
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
x_1362 = lean_ctor_get(x_1344, 0);
lean_inc(x_1362);
x_1363 = lean_ctor_get(x_1344, 1);
lean_inc(x_1363);
if (lean_is_exclusive(x_1344)) {
 lean_ctor_release(x_1344, 0);
 lean_ctor_release(x_1344, 1);
 x_1364 = x_1344;
} else {
 lean_dec_ref(x_1344);
 x_1364 = lean_box(0);
}
if (lean_is_scalar(x_1364)) {
 x_1365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1365 = x_1364;
}
lean_ctor_set(x_1365, 0, x_1362);
lean_ctor_set(x_1365, 1, x_1363);
return x_1365;
}
}
block_1325:
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1302 = lean_box(0);
if (lean_is_scalar(x_1297)) {
 x_1303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1303 = x_1297;
 lean_ctor_set_tag(x_1303, 1);
}
lean_ctor_set(x_1303, 0, x_1295);
lean_ctor_set(x_1303, 1, x_1302);
x_1304 = lean_array_mk(x_1303);
x_1305 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_1306 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1304, x_1300, x_1305, x_6, x_7, x_8, x_9, x_1301);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
lean_dec(x_1306);
lean_inc(x_1307);
x_1309 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1309, 0, x_1307);
lean_closure_set(x_1309, 1, x_1302);
x_1310 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1126, x_1309, x_6, x_7, x_8, x_9, x_1308);
if (lean_obj_tag(x_1310) == 0)
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_ctor_get(x_1310, 1);
lean_inc(x_1312);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 lean_ctor_release(x_1310, 1);
 x_1313 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1313 = lean_box(0);
}
if (lean_is_scalar(x_1291)) {
 x_1314 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1314 = x_1291;
 lean_ctor_set_tag(x_1314, 2);
}
lean_ctor_set(x_1314, 0, x_1307);
lean_ctor_set(x_1314, 1, x_1311);
if (lean_is_scalar(x_22)) {
 x_1315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1315 = x_22;
}
lean_ctor_set(x_1315, 0, x_1314);
if (lean_is_scalar(x_1313)) {
 x_1316 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1316 = x_1313;
}
lean_ctor_set(x_1316, 0, x_1315);
lean_ctor_set(x_1316, 1, x_1312);
return x_1316;
}
else
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
lean_dec(x_1307);
lean_dec(x_1291);
lean_dec(x_22);
x_1317 = lean_ctor_get(x_1310, 0);
lean_inc(x_1317);
x_1318 = lean_ctor_get(x_1310, 1);
lean_inc(x_1318);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 lean_ctor_release(x_1310, 1);
 x_1319 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1319 = lean_box(0);
}
if (lean_is_scalar(x_1319)) {
 x_1320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1320 = x_1319;
}
lean_ctor_set(x_1320, 0, x_1317);
lean_ctor_set(x_1320, 1, x_1318);
return x_1320;
}
}
else
{
lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; 
lean_dec(x_1291);
lean_dec(x_1126);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1321 = lean_ctor_get(x_1306, 0);
lean_inc(x_1321);
x_1322 = lean_ctor_get(x_1306, 1);
lean_inc(x_1322);
if (lean_is_exclusive(x_1306)) {
 lean_ctor_release(x_1306, 0);
 lean_ctor_release(x_1306, 1);
 x_1323 = x_1306;
} else {
 lean_dec_ref(x_1306);
 x_1323 = lean_box(0);
}
if (lean_is_scalar(x_1323)) {
 x_1324 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1324 = x_1323;
}
lean_ctor_set(x_1324, 0, x_1321);
lean_ctor_set(x_1324, 1, x_1322);
return x_1324;
}
}
}
else
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; 
lean_dec(x_1289);
x_1366 = lean_box(0);
x_1367 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1368 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1369 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1367, x_1126, x_1368, x_6, x_7, x_8, x_9, x_1290);
if (lean_obj_tag(x_1369) == 0)
{
lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; 
x_1370 = lean_ctor_get(x_1369, 0);
lean_inc(x_1370);
x_1371 = lean_ctor_get(x_1369, 1);
lean_inc(x_1371);
lean_dec(x_1369);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1372 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1370, x_6, x_7, x_8, x_9, x_1371);
if (lean_obj_tag(x_1372) == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; uint8_t x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1373 = lean_ctor_get(x_1372, 0);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_1372, 1);
lean_inc(x_1374);
lean_dec(x_1372);
x_1375 = lean_ctor_get(x_1373, 0);
lean_inc(x_1375);
x_1376 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1376 == 0)
{
lean_object* x_1389; 
lean_dec(x_27);
lean_dec(x_23);
x_1389 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1375, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1374);
if (lean_obj_tag(x_1389) == 0)
{
lean_object* x_1390; lean_object* x_1391; 
x_1390 = lean_ctor_get(x_1389, 1);
lean_inc(x_1390);
lean_dec(x_1389);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1391 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1390);
if (lean_obj_tag(x_1391) == 0)
{
lean_object* x_1392; lean_object* x_1393; 
x_1392 = lean_ctor_get(x_1391, 0);
lean_inc(x_1392);
x_1393 = lean_ctor_get(x_1391, 1);
lean_inc(x_1393);
lean_dec(x_1391);
x_1377 = x_1392;
x_1378 = x_1393;
goto block_1388;
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
lean_dec(x_1373);
lean_dec(x_1291);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1394 = lean_ctor_get(x_1391, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1391, 1);
lean_inc(x_1395);
if (lean_is_exclusive(x_1391)) {
 lean_ctor_release(x_1391, 0);
 lean_ctor_release(x_1391, 1);
 x_1396 = x_1391;
} else {
 lean_dec_ref(x_1391);
 x_1396 = lean_box(0);
}
if (lean_is_scalar(x_1396)) {
 x_1397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1397 = x_1396;
}
lean_ctor_set(x_1397, 0, x_1394);
lean_ctor_set(x_1397, 1, x_1395);
return x_1397;
}
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; 
lean_dec(x_1373);
lean_dec(x_1291);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1398 = lean_ctor_get(x_1389, 0);
lean_inc(x_1398);
x_1399 = lean_ctor_get(x_1389, 1);
lean_inc(x_1399);
if (lean_is_exclusive(x_1389)) {
 lean_ctor_release(x_1389, 0);
 lean_ctor_release(x_1389, 1);
 x_1400 = x_1389;
} else {
 lean_dec_ref(x_1389);
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
lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1402 = lean_array_get_size(x_23);
x_1403 = l_Array_toSubarray___rarg(x_23, x_27, x_1402);
x_1404 = l_Array_ofSubarray___rarg(x_1403);
lean_dec(x_1403);
x_1405 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_1405, 0, x_1375);
lean_ctor_set(x_1405, 1, x_1404);
x_1406 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1407 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1405, x_1406, x_6, x_7, x_8, x_9, x_1374);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
x_1408 = lean_ctor_get(x_1407, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1407, 1);
lean_inc(x_1409);
lean_dec(x_1407);
x_1410 = lean_ctor_get(x_1408, 0);
lean_inc(x_1410);
x_1411 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1410, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1409);
if (lean_obj_tag(x_1411) == 0)
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1412 = lean_ctor_get(x_1411, 1);
lean_inc(x_1412);
lean_dec(x_1411);
x_1413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1413, 0, x_1408);
lean_ctor_set(x_1413, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1414 = l_Lean_Compiler_LCNF_Simp_simp(x_1413, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1412);
if (lean_obj_tag(x_1414) == 0)
{
lean_object* x_1415; lean_object* x_1416; 
x_1415 = lean_ctor_get(x_1414, 0);
lean_inc(x_1415);
x_1416 = lean_ctor_get(x_1414, 1);
lean_inc(x_1416);
lean_dec(x_1414);
x_1377 = x_1415;
x_1378 = x_1416;
goto block_1388;
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
lean_dec(x_1373);
lean_dec(x_1291);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1417 = lean_ctor_get(x_1414, 0);
lean_inc(x_1417);
x_1418 = lean_ctor_get(x_1414, 1);
lean_inc(x_1418);
if (lean_is_exclusive(x_1414)) {
 lean_ctor_release(x_1414, 0);
 lean_ctor_release(x_1414, 1);
 x_1419 = x_1414;
} else {
 lean_dec_ref(x_1414);
 x_1419 = lean_box(0);
}
if (lean_is_scalar(x_1419)) {
 x_1420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1420 = x_1419;
}
lean_ctor_set(x_1420, 0, x_1417);
lean_ctor_set(x_1420, 1, x_1418);
return x_1420;
}
}
else
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
lean_dec(x_1408);
lean_dec(x_1373);
lean_dec(x_1291);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1421 = lean_ctor_get(x_1411, 0);
lean_inc(x_1421);
x_1422 = lean_ctor_get(x_1411, 1);
lean_inc(x_1422);
if (lean_is_exclusive(x_1411)) {
 lean_ctor_release(x_1411, 0);
 lean_ctor_release(x_1411, 1);
 x_1423 = x_1411;
} else {
 lean_dec_ref(x_1411);
 x_1423 = lean_box(0);
}
if (lean_is_scalar(x_1423)) {
 x_1424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1424 = x_1423;
}
lean_ctor_set(x_1424, 0, x_1421);
lean_ctor_set(x_1424, 1, x_1422);
return x_1424;
}
}
else
{
lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; 
lean_dec(x_1373);
lean_dec(x_1291);
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
x_1425 = lean_ctor_get(x_1407, 0);
lean_inc(x_1425);
x_1426 = lean_ctor_get(x_1407, 1);
lean_inc(x_1426);
if (lean_is_exclusive(x_1407)) {
 lean_ctor_release(x_1407, 0);
 lean_ctor_release(x_1407, 1);
 x_1427 = x_1407;
} else {
 lean_dec_ref(x_1407);
 x_1427 = lean_box(0);
}
if (lean_is_scalar(x_1427)) {
 x_1428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1428 = x_1427;
}
lean_ctor_set(x_1428, 0, x_1425);
lean_ctor_set(x_1428, 1, x_1426);
return x_1428;
}
}
block_1388:
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; 
x_1379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1379, 0, x_1373);
if (lean_is_scalar(x_1291)) {
 x_1380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1380 = x_1291;
 lean_ctor_set_tag(x_1380, 1);
}
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_1366);
x_1381 = lean_array_mk(x_1380);
x_1382 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1381, x_1377, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1378);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1381);
x_1383 = lean_ctor_get(x_1382, 0);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_1382, 1);
lean_inc(x_1384);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 x_1385 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1385 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1386 = x_22;
}
lean_ctor_set(x_1386, 0, x_1383);
if (lean_is_scalar(x_1385)) {
 x_1387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1387 = x_1385;
}
lean_ctor_set(x_1387, 0, x_1386);
lean_ctor_set(x_1387, 1, x_1384);
return x_1387;
}
}
else
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; 
lean_dec(x_1291);
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
x_1429 = lean_ctor_get(x_1372, 0);
lean_inc(x_1429);
x_1430 = lean_ctor_get(x_1372, 1);
lean_inc(x_1430);
if (lean_is_exclusive(x_1372)) {
 lean_ctor_release(x_1372, 0);
 lean_ctor_release(x_1372, 1);
 x_1431 = x_1372;
} else {
 lean_dec_ref(x_1372);
 x_1431 = lean_box(0);
}
if (lean_is_scalar(x_1431)) {
 x_1432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1432 = x_1431;
}
lean_ctor_set(x_1432, 0, x_1429);
lean_ctor_set(x_1432, 1, x_1430);
return x_1432;
}
}
else
{
lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; 
lean_dec(x_1291);
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
x_1433 = lean_ctor_get(x_1369, 0);
lean_inc(x_1433);
x_1434 = lean_ctor_get(x_1369, 1);
lean_inc(x_1434);
if (lean_is_exclusive(x_1369)) {
 lean_ctor_release(x_1369, 0);
 lean_ctor_release(x_1369, 1);
 x_1435 = x_1369;
} else {
 lean_dec_ref(x_1369);
 x_1435 = lean_box(0);
}
if (lean_is_scalar(x_1435)) {
 x_1436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1436 = x_1435;
}
lean_ctor_set(x_1436, 0, x_1433);
lean_ctor_set(x_1436, 1, x_1434);
return x_1436;
}
}
}
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
lean_dec(x_33);
lean_dec(x_21);
x_1437 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1127);
x_1438 = lean_ctor_get(x_1437, 1);
lean_inc(x_1438);
lean_dec(x_1437);
x_1439 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_1439, 0, x_3);
lean_closure_set(x_1439, 1, x_4);
lean_closure_set(x_1439, 2, x_5);
lean_closure_set(x_1439, 3, x_27);
lean_closure_set(x_1439, 4, x_24);
lean_closure_set(x_1439, 5, x_26);
lean_closure_set(x_1439, 6, x_2);
lean_closure_set(x_1439, 7, x_23);
x_1440 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1126, x_1439, x_6, x_7, x_8, x_9, x_1438);
if (lean_obj_tag(x_1440) == 0)
{
uint8_t x_1441; 
x_1441 = !lean_is_exclusive(x_1440);
if (x_1441 == 0)
{
lean_object* x_1442; lean_object* x_1443; 
x_1442 = lean_ctor_get(x_1440, 0);
if (lean_is_scalar(x_22)) {
 x_1443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1443 = x_22;
}
lean_ctor_set(x_1443, 0, x_1442);
lean_ctor_set(x_1440, 0, x_1443);
return x_1440;
}
else
{
lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1444 = lean_ctor_get(x_1440, 0);
x_1445 = lean_ctor_get(x_1440, 1);
lean_inc(x_1445);
lean_inc(x_1444);
lean_dec(x_1440);
if (lean_is_scalar(x_22)) {
 x_1446 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1446 = x_22;
}
lean_ctor_set(x_1446, 0, x_1444);
x_1447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1447, 0, x_1446);
lean_ctor_set(x_1447, 1, x_1445);
return x_1447;
}
}
else
{
uint8_t x_1448; 
lean_dec(x_22);
x_1448 = !lean_is_exclusive(x_1440);
if (x_1448 == 0)
{
return x_1440;
}
else
{
lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1449 = lean_ctor_get(x_1440, 0);
x_1450 = lean_ctor_get(x_1440, 1);
lean_inc(x_1450);
lean_inc(x_1449);
lean_dec(x_1440);
x_1451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1451, 0, x_1449);
lean_ctor_set(x_1451, 1, x_1450);
return x_1451;
}
}
}
}
else
{
uint8_t x_1452; 
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
x_1452 = !lean_is_exclusive(x_1125);
if (x_1452 == 0)
{
return x_1125;
}
else
{
lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1453 = lean_ctor_get(x_1125, 0);
x_1454 = lean_ctor_get(x_1125, 1);
lean_inc(x_1454);
lean_inc(x_1453);
lean_dec(x_1125);
x_1455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set(x_1455, 1, x_1454);
return x_1455;
}
}
}
}
else
{
uint8_t x_1475; 
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
x_1475 = !lean_is_exclusive(x_1121);
if (x_1475 == 0)
{
return x_1121;
}
else
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
x_1476 = lean_ctor_get(x_1121, 0);
x_1477 = lean_ctor_get(x_1121, 1);
lean_inc(x_1477);
lean_inc(x_1476);
lean_dec(x_1121);
x_1478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1478, 0, x_1476);
lean_ctor_set(x_1478, 1, x_1477);
return x_1478;
}
}
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; uint8_t x_1486; lean_object* x_1487; 
x_1479 = lean_ctor_get(x_3, 0);
x_1480 = lean_ctor_get(x_3, 1);
x_1481 = lean_ctor_get(x_3, 2);
x_1482 = lean_ctor_get(x_3, 3);
lean_inc(x_1482);
lean_inc(x_1481);
lean_inc(x_1480);
lean_inc(x_1479);
lean_dec(x_3);
lean_inc(x_1111);
x_1483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1483, 0, x_1111);
lean_ctor_set(x_1483, 1, x_1481);
x_1484 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_1482, x_1111, x_1113);
x_1485 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1485, 0, x_1479);
lean_ctor_set(x_1485, 1, x_1480);
lean_ctor_set(x_1485, 2, x_1483);
lean_ctor_set(x_1485, 3, x_1484);
x_1486 = 0;
lean_inc(x_33);
x_1487 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1486, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1114);
lean_dec(x_29);
if (lean_obj_tag(x_1487) == 0)
{
lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; uint8_t x_1666; 
x_1488 = lean_ctor_get(x_1487, 0);
lean_inc(x_1488);
x_1489 = lean_ctor_get(x_1487, 1);
lean_inc(x_1489);
lean_dec(x_1487);
x_1666 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_1666 == 0)
{
lean_object* x_1667; 
x_1667 = lean_box(0);
x_1490 = x_1667;
goto block_1665;
}
else
{
uint8_t x_1668; 
x_1668 = lean_nat_dec_eq(x_24, x_27);
if (x_1668 == 0)
{
lean_object* x_1669; 
x_1669 = lean_box(0);
x_1490 = x_1669;
goto block_1665;
}
else
{
lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_1670 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1489);
x_1671 = lean_ctor_get(x_1670, 1);
lean_inc(x_1671);
lean_dec(x_1670);
x_1672 = l_Lean_Compiler_LCNF_Simp_simp(x_1488, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1671);
if (lean_obj_tag(x_1672) == 0)
{
lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
x_1673 = lean_ctor_get(x_1672, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1672, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_1672)) {
 lean_ctor_release(x_1672, 0);
 lean_ctor_release(x_1672, 1);
 x_1675 = x_1672;
} else {
 lean_dec_ref(x_1672);
 x_1675 = lean_box(0);
}
x_1676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1676, 0, x_1673);
if (lean_is_scalar(x_1675)) {
 x_1677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1677 = x_1675;
}
lean_ctor_set(x_1677, 0, x_1676);
lean_ctor_set(x_1677, 1, x_1674);
return x_1677;
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
x_1678 = lean_ctor_get(x_1672, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1672, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1672)) {
 lean_ctor_release(x_1672, 0);
 lean_ctor_release(x_1672, 1);
 x_1680 = x_1672;
} else {
 lean_dec_ref(x_1672);
 x_1680 = lean_box(0);
}
if (lean_is_scalar(x_1680)) {
 x_1681 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1681 = x_1680;
}
lean_ctor_set(x_1681, 0, x_1678);
lean_ctor_set(x_1681, 1, x_1679);
return x_1681;
}
}
}
block_1665:
{
lean_object* x_1491; 
lean_dec(x_1490);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1485);
x_1491 = l_Lean_Compiler_LCNF_Simp_simp(x_1488, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1489);
if (lean_obj_tag(x_1491) == 0)
{
lean_object* x_1492; lean_object* x_1493; uint8_t x_1494; 
x_1492 = lean_ctor_get(x_1491, 0);
lean_inc(x_1492);
x_1493 = lean_ctor_get(x_1491, 1);
lean_inc(x_1493);
lean_dec(x_1491);
lean_inc(x_1492);
x_1494 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1492);
if (x_1494 == 0)
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; uint8_t x_1504; 
x_1495 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1493);
x_1496 = lean_ctor_get(x_1495, 1);
lean_inc(x_1496);
if (lean_is_exclusive(x_1495)) {
 lean_ctor_release(x_1495, 0);
 lean_ctor_release(x_1495, 1);
 x_1497 = x_1495;
} else {
 lean_dec_ref(x_1495);
 x_1497 = lean_box(0);
}
x_1498 = lean_ctor_get(x_21, 2);
lean_inc(x_1498);
lean_dec(x_21);
x_1499 = l_Lean_Compiler_LCNF_inferAppType(x_1498, x_33, x_6, x_7, x_8, x_9, x_1496);
x_1500 = lean_ctor_get(x_1499, 0);
lean_inc(x_1500);
x_1501 = lean_ctor_get(x_1499, 1);
lean_inc(x_1501);
if (lean_is_exclusive(x_1499)) {
 lean_ctor_release(x_1499, 0);
 lean_ctor_release(x_1499, 1);
 x_1502 = x_1499;
} else {
 lean_dec_ref(x_1499);
 x_1502 = lean_box(0);
}
lean_inc(x_1500);
x_1503 = l_Lean_Expr_headBeta(x_1500);
x_1504 = l_Lean_Expr_isForall(x_1503);
lean_dec(x_1503);
if (x_1504 == 0)
{
lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; uint8_t x_1510; lean_object* x_1511; lean_object* x_1512; 
x_1505 = l_Lean_Compiler_LCNF_mkAuxParam(x_1500, x_1486, x_6, x_7, x_8, x_9, x_1501);
x_1506 = lean_ctor_get(x_1505, 0);
lean_inc(x_1506);
x_1507 = lean_ctor_get(x_1505, 1);
lean_inc(x_1507);
if (lean_is_exclusive(x_1505)) {
 lean_ctor_release(x_1505, 0);
 lean_ctor_release(x_1505, 1);
 x_1508 = x_1505;
} else {
 lean_dec_ref(x_1505);
 x_1508 = lean_box(0);
}
x_1509 = lean_ctor_get(x_1506, 0);
lean_inc(x_1509);
x_1510 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1510 == 0)
{
lean_object* x_1537; 
lean_dec(x_1497);
lean_dec(x_27);
lean_dec(x_23);
x_1537 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1509, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1507);
if (lean_obj_tag(x_1537) == 0)
{
lean_object* x_1538; lean_object* x_1539; 
x_1538 = lean_ctor_get(x_1537, 1);
lean_inc(x_1538);
lean_dec(x_1537);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1539 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1538);
if (lean_obj_tag(x_1539) == 0)
{
lean_object* x_1540; lean_object* x_1541; 
x_1540 = lean_ctor_get(x_1539, 0);
lean_inc(x_1540);
x_1541 = lean_ctor_get(x_1539, 1);
lean_inc(x_1541);
lean_dec(x_1539);
x_1511 = x_1540;
x_1512 = x_1541;
goto block_1536;
}
else
{
lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1542 = lean_ctor_get(x_1539, 0);
lean_inc(x_1542);
x_1543 = lean_ctor_get(x_1539, 1);
lean_inc(x_1543);
if (lean_is_exclusive(x_1539)) {
 lean_ctor_release(x_1539, 0);
 lean_ctor_release(x_1539, 1);
 x_1544 = x_1539;
} else {
 lean_dec_ref(x_1539);
 x_1544 = lean_box(0);
}
if (lean_is_scalar(x_1544)) {
 x_1545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1545 = x_1544;
}
lean_ctor_set(x_1545, 0, x_1542);
lean_ctor_set(x_1545, 1, x_1543);
return x_1545;
}
}
else
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1546 = lean_ctor_get(x_1537, 0);
lean_inc(x_1546);
x_1547 = lean_ctor_get(x_1537, 1);
lean_inc(x_1547);
if (lean_is_exclusive(x_1537)) {
 lean_ctor_release(x_1537, 0);
 lean_ctor_release(x_1537, 1);
 x_1548 = x_1537;
} else {
 lean_dec_ref(x_1537);
 x_1548 = lean_box(0);
}
if (lean_is_scalar(x_1548)) {
 x_1549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1549 = x_1548;
}
lean_ctor_set(x_1549, 0, x_1546);
lean_ctor_set(x_1549, 1, x_1547);
return x_1549;
}
}
else
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; 
x_1550 = lean_array_get_size(x_23);
x_1551 = l_Array_toSubarray___rarg(x_23, x_27, x_1550);
x_1552 = l_Array_ofSubarray___rarg(x_1551);
lean_dec(x_1551);
if (lean_is_scalar(x_1497)) {
 x_1553 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1553 = x_1497;
 lean_ctor_set_tag(x_1553, 4);
}
lean_ctor_set(x_1553, 0, x_1509);
lean_ctor_set(x_1553, 1, x_1552);
x_1554 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1555 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1553, x_1554, x_6, x_7, x_8, x_9, x_1507);
if (lean_obj_tag(x_1555) == 0)
{
lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; 
x_1556 = lean_ctor_get(x_1555, 0);
lean_inc(x_1556);
x_1557 = lean_ctor_get(x_1555, 1);
lean_inc(x_1557);
lean_dec(x_1555);
x_1558 = lean_ctor_get(x_1556, 0);
lean_inc(x_1558);
x_1559 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1558, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1557);
if (lean_obj_tag(x_1559) == 0)
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
x_1560 = lean_ctor_get(x_1559, 1);
lean_inc(x_1560);
lean_dec(x_1559);
x_1561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1561, 0, x_1556);
lean_ctor_set(x_1561, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1562 = l_Lean_Compiler_LCNF_Simp_simp(x_1561, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1560);
if (lean_obj_tag(x_1562) == 0)
{
lean_object* x_1563; lean_object* x_1564; 
x_1563 = lean_ctor_get(x_1562, 0);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1562, 1);
lean_inc(x_1564);
lean_dec(x_1562);
x_1511 = x_1563;
x_1512 = x_1564;
goto block_1536;
}
else
{
lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1565 = lean_ctor_get(x_1562, 0);
lean_inc(x_1565);
x_1566 = lean_ctor_get(x_1562, 1);
lean_inc(x_1566);
if (lean_is_exclusive(x_1562)) {
 lean_ctor_release(x_1562, 0);
 lean_ctor_release(x_1562, 1);
 x_1567 = x_1562;
} else {
 lean_dec_ref(x_1562);
 x_1567 = lean_box(0);
}
if (lean_is_scalar(x_1567)) {
 x_1568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1568 = x_1567;
}
lean_ctor_set(x_1568, 0, x_1565);
lean_ctor_set(x_1568, 1, x_1566);
return x_1568;
}
}
else
{
lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; 
lean_dec(x_1556);
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1569 = lean_ctor_get(x_1559, 0);
lean_inc(x_1569);
x_1570 = lean_ctor_get(x_1559, 1);
lean_inc(x_1570);
if (lean_is_exclusive(x_1559)) {
 lean_ctor_release(x_1559, 0);
 lean_ctor_release(x_1559, 1);
 x_1571 = x_1559;
} else {
 lean_dec_ref(x_1559);
 x_1571 = lean_box(0);
}
if (lean_is_scalar(x_1571)) {
 x_1572 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1572 = x_1571;
}
lean_ctor_set(x_1572, 0, x_1569);
lean_ctor_set(x_1572, 1, x_1570);
return x_1572;
}
}
else
{
lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
lean_dec(x_1508);
lean_dec(x_1506);
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_1485);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1573 = lean_ctor_get(x_1555, 0);
lean_inc(x_1573);
x_1574 = lean_ctor_get(x_1555, 1);
lean_inc(x_1574);
if (lean_is_exclusive(x_1555)) {
 lean_ctor_release(x_1555, 0);
 lean_ctor_release(x_1555, 1);
 x_1575 = x_1555;
} else {
 lean_dec_ref(x_1555);
 x_1575 = lean_box(0);
}
if (lean_is_scalar(x_1575)) {
 x_1576 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1576 = x_1575;
}
lean_ctor_set(x_1576, 0, x_1573);
lean_ctor_set(x_1576, 1, x_1574);
return x_1576;
}
}
block_1536:
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; 
x_1513 = lean_box(0);
if (lean_is_scalar(x_1508)) {
 x_1514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1514 = x_1508;
 lean_ctor_set_tag(x_1514, 1);
}
lean_ctor_set(x_1514, 0, x_1506);
lean_ctor_set(x_1514, 1, x_1513);
x_1515 = lean_array_mk(x_1514);
x_1516 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_1517 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1515, x_1511, x_1516, x_6, x_7, x_8, x_9, x_1512);
if (lean_obj_tag(x_1517) == 0)
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; 
x_1518 = lean_ctor_get(x_1517, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1517, 1);
lean_inc(x_1519);
lean_dec(x_1517);
lean_inc(x_1518);
x_1520 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1520, 0, x_1518);
lean_closure_set(x_1520, 1, x_1513);
x_1521 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1492, x_1520, x_6, x_7, x_8, x_9, x_1519);
if (lean_obj_tag(x_1521) == 0)
{
lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; 
x_1522 = lean_ctor_get(x_1521, 0);
lean_inc(x_1522);
x_1523 = lean_ctor_get(x_1521, 1);
lean_inc(x_1523);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1524 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1524 = lean_box(0);
}
if (lean_is_scalar(x_1502)) {
 x_1525 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1525 = x_1502;
 lean_ctor_set_tag(x_1525, 2);
}
lean_ctor_set(x_1525, 0, x_1518);
lean_ctor_set(x_1525, 1, x_1522);
if (lean_is_scalar(x_22)) {
 x_1526 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1526 = x_22;
}
lean_ctor_set(x_1526, 0, x_1525);
if (lean_is_scalar(x_1524)) {
 x_1527 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1527 = x_1524;
}
lean_ctor_set(x_1527, 0, x_1526);
lean_ctor_set(x_1527, 1, x_1523);
return x_1527;
}
else
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
lean_dec(x_1518);
lean_dec(x_1502);
lean_dec(x_22);
x_1528 = lean_ctor_get(x_1521, 0);
lean_inc(x_1528);
x_1529 = lean_ctor_get(x_1521, 1);
lean_inc(x_1529);
if (lean_is_exclusive(x_1521)) {
 lean_ctor_release(x_1521, 0);
 lean_ctor_release(x_1521, 1);
 x_1530 = x_1521;
} else {
 lean_dec_ref(x_1521);
 x_1530 = lean_box(0);
}
if (lean_is_scalar(x_1530)) {
 x_1531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1531 = x_1530;
}
lean_ctor_set(x_1531, 0, x_1528);
lean_ctor_set(x_1531, 1, x_1529);
return x_1531;
}
}
else
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; 
lean_dec(x_1502);
lean_dec(x_1492);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1532 = lean_ctor_get(x_1517, 0);
lean_inc(x_1532);
x_1533 = lean_ctor_get(x_1517, 1);
lean_inc(x_1533);
if (lean_is_exclusive(x_1517)) {
 lean_ctor_release(x_1517, 0);
 lean_ctor_release(x_1517, 1);
 x_1534 = x_1517;
} else {
 lean_dec_ref(x_1517);
 x_1534 = lean_box(0);
}
if (lean_is_scalar(x_1534)) {
 x_1535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1535 = x_1534;
}
lean_ctor_set(x_1535, 0, x_1532);
lean_ctor_set(x_1535, 1, x_1533);
return x_1535;
}
}
}
else
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; 
lean_dec(x_1500);
x_1577 = lean_box(0);
x_1578 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1579 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1580 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1578, x_1492, x_1579, x_6, x_7, x_8, x_9, x_1501);
if (lean_obj_tag(x_1580) == 0)
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1581 = lean_ctor_get(x_1580, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_1580, 1);
lean_inc(x_1582);
lean_dec(x_1580);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1583 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1581, x_6, x_7, x_8, x_9, x_1582);
if (lean_obj_tag(x_1583) == 0)
{
lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; uint8_t x_1587; lean_object* x_1588; lean_object* x_1589; 
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1583, 1);
lean_inc(x_1585);
lean_dec(x_1583);
x_1586 = lean_ctor_get(x_1584, 0);
lean_inc(x_1586);
x_1587 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1587 == 0)
{
lean_object* x_1600; 
lean_dec(x_1497);
lean_dec(x_27);
lean_dec(x_23);
x_1600 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1586, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1585);
if (lean_obj_tag(x_1600) == 0)
{
lean_object* x_1601; lean_object* x_1602; 
x_1601 = lean_ctor_get(x_1600, 1);
lean_inc(x_1601);
lean_dec(x_1600);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1485);
x_1602 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1601);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; lean_object* x_1604; 
x_1603 = lean_ctor_get(x_1602, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1602, 1);
lean_inc(x_1604);
lean_dec(x_1602);
x_1588 = x_1603;
x_1589 = x_1604;
goto block_1599;
}
else
{
lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
lean_dec(x_1584);
lean_dec(x_1502);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1605 = lean_ctor_get(x_1602, 0);
lean_inc(x_1605);
x_1606 = lean_ctor_get(x_1602, 1);
lean_inc(x_1606);
if (lean_is_exclusive(x_1602)) {
 lean_ctor_release(x_1602, 0);
 lean_ctor_release(x_1602, 1);
 x_1607 = x_1602;
} else {
 lean_dec_ref(x_1602);
 x_1607 = lean_box(0);
}
if (lean_is_scalar(x_1607)) {
 x_1608 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1608 = x_1607;
}
lean_ctor_set(x_1608, 0, x_1605);
lean_ctor_set(x_1608, 1, x_1606);
return x_1608;
}
}
else
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; 
lean_dec(x_1584);
lean_dec(x_1502);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1609 = lean_ctor_get(x_1600, 0);
lean_inc(x_1609);
x_1610 = lean_ctor_get(x_1600, 1);
lean_inc(x_1610);
if (lean_is_exclusive(x_1600)) {
 lean_ctor_release(x_1600, 0);
 lean_ctor_release(x_1600, 1);
 x_1611 = x_1600;
} else {
 lean_dec_ref(x_1600);
 x_1611 = lean_box(0);
}
if (lean_is_scalar(x_1611)) {
 x_1612 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1612 = x_1611;
}
lean_ctor_set(x_1612, 0, x_1609);
lean_ctor_set(x_1612, 1, x_1610);
return x_1612;
}
}
else
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; 
x_1613 = lean_array_get_size(x_23);
x_1614 = l_Array_toSubarray___rarg(x_23, x_27, x_1613);
x_1615 = l_Array_ofSubarray___rarg(x_1614);
lean_dec(x_1614);
if (lean_is_scalar(x_1497)) {
 x_1616 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1616 = x_1497;
 lean_ctor_set_tag(x_1616, 4);
}
lean_ctor_set(x_1616, 0, x_1586);
lean_ctor_set(x_1616, 1, x_1615);
x_1617 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1618 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1616, x_1617, x_6, x_7, x_8, x_9, x_1585);
if (lean_obj_tag(x_1618) == 0)
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; 
x_1619 = lean_ctor_get(x_1618, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_1618, 1);
lean_inc(x_1620);
lean_dec(x_1618);
x_1621 = lean_ctor_get(x_1619, 0);
lean_inc(x_1621);
x_1622 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1621, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1620);
if (lean_obj_tag(x_1622) == 0)
{
lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; 
x_1623 = lean_ctor_get(x_1622, 1);
lean_inc(x_1623);
lean_dec(x_1622);
x_1624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1624, 0, x_1619);
lean_ctor_set(x_1624, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1485);
x_1625 = l_Lean_Compiler_LCNF_Simp_simp(x_1624, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1623);
if (lean_obj_tag(x_1625) == 0)
{
lean_object* x_1626; lean_object* x_1627; 
x_1626 = lean_ctor_get(x_1625, 0);
lean_inc(x_1626);
x_1627 = lean_ctor_get(x_1625, 1);
lean_inc(x_1627);
lean_dec(x_1625);
x_1588 = x_1626;
x_1589 = x_1627;
goto block_1599;
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_dec(x_1584);
lean_dec(x_1502);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1628 = lean_ctor_get(x_1625, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1625, 1);
lean_inc(x_1629);
if (lean_is_exclusive(x_1625)) {
 lean_ctor_release(x_1625, 0);
 lean_ctor_release(x_1625, 1);
 x_1630 = x_1625;
} else {
 lean_dec_ref(x_1625);
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
else
{
lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; 
lean_dec(x_1619);
lean_dec(x_1584);
lean_dec(x_1502);
lean_dec(x_1485);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1632 = lean_ctor_get(x_1622, 0);
lean_inc(x_1632);
x_1633 = lean_ctor_get(x_1622, 1);
lean_inc(x_1633);
if (lean_is_exclusive(x_1622)) {
 lean_ctor_release(x_1622, 0);
 lean_ctor_release(x_1622, 1);
 x_1634 = x_1622;
} else {
 lean_dec_ref(x_1622);
 x_1634 = lean_box(0);
}
if (lean_is_scalar(x_1634)) {
 x_1635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1635 = x_1634;
}
lean_ctor_set(x_1635, 0, x_1632);
lean_ctor_set(x_1635, 1, x_1633);
return x_1635;
}
}
else
{
lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
lean_dec(x_1584);
lean_dec(x_1502);
lean_dec(x_1485);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1636 = lean_ctor_get(x_1618, 0);
lean_inc(x_1636);
x_1637 = lean_ctor_get(x_1618, 1);
lean_inc(x_1637);
if (lean_is_exclusive(x_1618)) {
 lean_ctor_release(x_1618, 0);
 lean_ctor_release(x_1618, 1);
 x_1638 = x_1618;
} else {
 lean_dec_ref(x_1618);
 x_1638 = lean_box(0);
}
if (lean_is_scalar(x_1638)) {
 x_1639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1639 = x_1638;
}
lean_ctor_set(x_1639, 0, x_1636);
lean_ctor_set(x_1639, 1, x_1637);
return x_1639;
}
}
block_1599:
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; 
x_1590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1590, 0, x_1584);
if (lean_is_scalar(x_1502)) {
 x_1591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1591 = x_1502;
 lean_ctor_set_tag(x_1591, 1);
}
lean_ctor_set(x_1591, 0, x_1590);
lean_ctor_set(x_1591, 1, x_1577);
x_1592 = lean_array_mk(x_1591);
x_1593 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1592, x_1588, x_1485, x_4, x_5, x_6, x_7, x_8, x_9, x_1589);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1485);
lean_dec(x_1592);
x_1594 = lean_ctor_get(x_1593, 0);
lean_inc(x_1594);
x_1595 = lean_ctor_get(x_1593, 1);
lean_inc(x_1595);
if (lean_is_exclusive(x_1593)) {
 lean_ctor_release(x_1593, 0);
 lean_ctor_release(x_1593, 1);
 x_1596 = x_1593;
} else {
 lean_dec_ref(x_1593);
 x_1596 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1597 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1597 = x_22;
}
lean_ctor_set(x_1597, 0, x_1594);
if (lean_is_scalar(x_1596)) {
 x_1598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1598 = x_1596;
}
lean_ctor_set(x_1598, 0, x_1597);
lean_ctor_set(x_1598, 1, x_1595);
return x_1598;
}
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; 
lean_dec(x_1502);
lean_dec(x_1497);
lean_dec(x_1485);
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
x_1640 = lean_ctor_get(x_1583, 0);
lean_inc(x_1640);
x_1641 = lean_ctor_get(x_1583, 1);
lean_inc(x_1641);
if (lean_is_exclusive(x_1583)) {
 lean_ctor_release(x_1583, 0);
 lean_ctor_release(x_1583, 1);
 x_1642 = x_1583;
} else {
 lean_dec_ref(x_1583);
 x_1642 = lean_box(0);
}
if (lean_is_scalar(x_1642)) {
 x_1643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1643 = x_1642;
}
lean_ctor_set(x_1643, 0, x_1640);
lean_ctor_set(x_1643, 1, x_1641);
return x_1643;
}
}
else
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
lean_dec(x_1502);
lean_dec(x_1497);
lean_dec(x_1485);
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
x_1644 = lean_ctor_get(x_1580, 0);
lean_inc(x_1644);
x_1645 = lean_ctor_get(x_1580, 1);
lean_inc(x_1645);
if (lean_is_exclusive(x_1580)) {
 lean_ctor_release(x_1580, 0);
 lean_ctor_release(x_1580, 1);
 x_1646 = x_1580;
} else {
 lean_dec_ref(x_1580);
 x_1646 = lean_box(0);
}
if (lean_is_scalar(x_1646)) {
 x_1647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1647 = x_1646;
}
lean_ctor_set(x_1647, 0, x_1644);
lean_ctor_set(x_1647, 1, x_1645);
return x_1647;
}
}
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; 
lean_dec(x_33);
lean_dec(x_21);
x_1648 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1493);
x_1649 = lean_ctor_get(x_1648, 1);
lean_inc(x_1649);
lean_dec(x_1648);
x_1650 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_1650, 0, x_1485);
lean_closure_set(x_1650, 1, x_4);
lean_closure_set(x_1650, 2, x_5);
lean_closure_set(x_1650, 3, x_27);
lean_closure_set(x_1650, 4, x_24);
lean_closure_set(x_1650, 5, x_26);
lean_closure_set(x_1650, 6, x_2);
lean_closure_set(x_1650, 7, x_23);
x_1651 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1492, x_1650, x_6, x_7, x_8, x_9, x_1649);
if (lean_obj_tag(x_1651) == 0)
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; 
x_1652 = lean_ctor_get(x_1651, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1651, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1651)) {
 lean_ctor_release(x_1651, 0);
 lean_ctor_release(x_1651, 1);
 x_1654 = x_1651;
} else {
 lean_dec_ref(x_1651);
 x_1654 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1655 = x_22;
}
lean_ctor_set(x_1655, 0, x_1652);
if (lean_is_scalar(x_1654)) {
 x_1656 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1656 = x_1654;
}
lean_ctor_set(x_1656, 0, x_1655);
lean_ctor_set(x_1656, 1, x_1653);
return x_1656;
}
else
{
lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; 
lean_dec(x_22);
x_1657 = lean_ctor_get(x_1651, 0);
lean_inc(x_1657);
x_1658 = lean_ctor_get(x_1651, 1);
lean_inc(x_1658);
if (lean_is_exclusive(x_1651)) {
 lean_ctor_release(x_1651, 0);
 lean_ctor_release(x_1651, 1);
 x_1659 = x_1651;
} else {
 lean_dec_ref(x_1651);
 x_1659 = lean_box(0);
}
if (lean_is_scalar(x_1659)) {
 x_1660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1660 = x_1659;
}
lean_ctor_set(x_1660, 0, x_1657);
lean_ctor_set(x_1660, 1, x_1658);
return x_1660;
}
}
}
else
{
lean_object* x_1661; lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; 
lean_dec(x_1485);
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
x_1661 = lean_ctor_get(x_1491, 0);
lean_inc(x_1661);
x_1662 = lean_ctor_get(x_1491, 1);
lean_inc(x_1662);
if (lean_is_exclusive(x_1491)) {
 lean_ctor_release(x_1491, 0);
 lean_ctor_release(x_1491, 1);
 x_1663 = x_1491;
} else {
 lean_dec_ref(x_1491);
 x_1663 = lean_box(0);
}
if (lean_is_scalar(x_1663)) {
 x_1664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1664 = x_1663;
}
lean_ctor_set(x_1664, 0, x_1661);
lean_ctor_set(x_1664, 1, x_1662);
return x_1664;
}
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec(x_1485);
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
x_1682 = lean_ctor_get(x_1487, 0);
lean_inc(x_1682);
x_1683 = lean_ctor_get(x_1487, 1);
lean_inc(x_1683);
if (lean_is_exclusive(x_1487)) {
 lean_ctor_release(x_1487, 0);
 lean_ctor_release(x_1487, 1);
 x_1684 = x_1487;
} else {
 lean_dec_ref(x_1487);
 x_1684 = lean_box(0);
}
if (lean_is_scalar(x_1684)) {
 x_1685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1685 = x_1684;
}
lean_ctor_set(x_1685, 0, x_1682);
lean_ctor_set(x_1685, 1, x_1683);
return x_1685;
}
}
}
else
{
uint8_t x_1686; 
lean_dec(x_1111);
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
x_1686 = !lean_is_exclusive(x_1112);
if (x_1686 == 0)
{
return x_1112;
}
else
{
lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
x_1687 = lean_ctor_get(x_1112, 0);
x_1688 = lean_ctor_get(x_1112, 1);
lean_inc(x_1688);
lean_inc(x_1687);
lean_dec(x_1112);
x_1689 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1689, 0, x_1687);
lean_ctor_set(x_1689, 1, x_1688);
return x_1689;
}
}
}
default: 
{
lean_object* x_1690; uint8_t x_1691; lean_object* x_1692; 
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_1690 = x_11;
} else {
 lean_dec_ref(x_11);
 x_1690 = lean_box(0);
}
x_1691 = 0;
lean_inc(x_33);
x_1692 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_29, x_30, x_33, x_1691, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_29);
if (lean_obj_tag(x_1692) == 0)
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; uint8_t x_2028; 
x_1693 = lean_ctor_get(x_1692, 0);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1692, 1);
lean_inc(x_1694);
lean_dec(x_1692);
x_2028 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_26);
if (x_2028 == 0)
{
lean_object* x_2029; 
x_2029 = lean_box(0);
x_1695 = x_2029;
goto block_2027;
}
else
{
uint8_t x_2030; 
x_2030 = lean_nat_dec_eq(x_24, x_27);
if (x_2030 == 0)
{
lean_object* x_2031; 
x_2031 = lean_box(0);
x_1695 = x_2031;
goto block_2027;
}
else
{
lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; 
lean_dec(x_1690);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_2032 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1694);
x_2033 = lean_ctor_get(x_2032, 1);
lean_inc(x_2033);
lean_dec(x_2032);
x_2034 = l_Lean_Compiler_LCNF_Simp_simp(x_1693, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2033);
if (lean_obj_tag(x_2034) == 0)
{
uint8_t x_2035; 
x_2035 = !lean_is_exclusive(x_2034);
if (x_2035 == 0)
{
lean_object* x_2036; lean_object* x_2037; 
x_2036 = lean_ctor_get(x_2034, 0);
x_2037 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2037, 0, x_2036);
lean_ctor_set(x_2034, 0, x_2037);
return x_2034;
}
else
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; 
x_2038 = lean_ctor_get(x_2034, 0);
x_2039 = lean_ctor_get(x_2034, 1);
lean_inc(x_2039);
lean_inc(x_2038);
lean_dec(x_2034);
x_2040 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2040, 0, x_2038);
x_2041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2041, 0, x_2040);
lean_ctor_set(x_2041, 1, x_2039);
return x_2041;
}
}
else
{
uint8_t x_2042; 
x_2042 = !lean_is_exclusive(x_2034);
if (x_2042 == 0)
{
return x_2034;
}
else
{
lean_object* x_2043; lean_object* x_2044; lean_object* x_2045; 
x_2043 = lean_ctor_get(x_2034, 0);
x_2044 = lean_ctor_get(x_2034, 1);
lean_inc(x_2044);
lean_inc(x_2043);
lean_dec(x_2034);
x_2045 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2045, 0, x_2043);
lean_ctor_set(x_2045, 1, x_2044);
return x_2045;
}
}
}
}
block_2027:
{
lean_object* x_1696; 
lean_dec(x_1695);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1696 = l_Lean_Compiler_LCNF_Simp_simp(x_1693, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1694);
if (lean_obj_tag(x_1696) == 0)
{
lean_object* x_1697; lean_object* x_1698; uint8_t x_1699; 
x_1697 = lean_ctor_get(x_1696, 0);
lean_inc(x_1697);
x_1698 = lean_ctor_get(x_1696, 1);
lean_inc(x_1698);
lean_dec(x_1696);
lean_inc(x_1697);
x_1699 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1697);
if (x_1699 == 0)
{
lean_object* x_1700; uint8_t x_1701; 
x_1700 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1698);
x_1701 = !lean_is_exclusive(x_1700);
if (x_1701 == 0)
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; uint8_t x_1710; 
x_1702 = lean_ctor_get(x_1700, 1);
x_1703 = lean_ctor_get(x_1700, 0);
lean_dec(x_1703);
x_1704 = lean_ctor_get(x_21, 2);
lean_inc(x_1704);
lean_dec(x_21);
x_1705 = l_Lean_Compiler_LCNF_inferAppType(x_1704, x_33, x_6, x_7, x_8, x_9, x_1702);
x_1706 = lean_ctor_get(x_1705, 0);
lean_inc(x_1706);
x_1707 = lean_ctor_get(x_1705, 1);
lean_inc(x_1707);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1708 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1708 = lean_box(0);
}
lean_inc(x_1706);
x_1709 = l_Lean_Expr_headBeta(x_1706);
x_1710 = l_Lean_Expr_isForall(x_1709);
lean_dec(x_1709);
if (x_1710 == 0)
{
lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; uint8_t x_1716; lean_object* x_1717; lean_object* x_1718; 
x_1711 = l_Lean_Compiler_LCNF_mkAuxParam(x_1706, x_1691, x_6, x_7, x_8, x_9, x_1707);
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
if (lean_is_exclusive(x_1711)) {
 lean_ctor_release(x_1711, 0);
 lean_ctor_release(x_1711, 1);
 x_1714 = x_1711;
} else {
 lean_dec_ref(x_1711);
 x_1714 = lean_box(0);
}
x_1715 = lean_ctor_get(x_1712, 0);
lean_inc(x_1715);
x_1716 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1716 == 0)
{
lean_object* x_1746; 
lean_free_object(x_1700);
lean_dec(x_1690);
lean_dec(x_27);
lean_dec(x_23);
x_1746 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1715, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1713);
if (lean_obj_tag(x_1746) == 0)
{
lean_object* x_1747; lean_object* x_1748; 
x_1747 = lean_ctor_get(x_1746, 1);
lean_inc(x_1747);
lean_dec(x_1746);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1748 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1747);
if (lean_obj_tag(x_1748) == 0)
{
lean_object* x_1749; lean_object* x_1750; 
x_1749 = lean_ctor_get(x_1748, 0);
lean_inc(x_1749);
x_1750 = lean_ctor_get(x_1748, 1);
lean_inc(x_1750);
lean_dec(x_1748);
x_1717 = x_1749;
x_1718 = x_1750;
goto block_1745;
}
else
{
uint8_t x_1751; 
lean_dec(x_1714);
lean_dec(x_1712);
lean_dec(x_1708);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1751 = !lean_is_exclusive(x_1748);
if (x_1751 == 0)
{
return x_1748;
}
else
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
x_1752 = lean_ctor_get(x_1748, 0);
x_1753 = lean_ctor_get(x_1748, 1);
lean_inc(x_1753);
lean_inc(x_1752);
lean_dec(x_1748);
x_1754 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1754, 0, x_1752);
lean_ctor_set(x_1754, 1, x_1753);
return x_1754;
}
}
}
else
{
uint8_t x_1755; 
lean_dec(x_1714);
lean_dec(x_1712);
lean_dec(x_1708);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1755 = !lean_is_exclusive(x_1746);
if (x_1755 == 0)
{
return x_1746;
}
else
{
lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; 
x_1756 = lean_ctor_get(x_1746, 0);
x_1757 = lean_ctor_get(x_1746, 1);
lean_inc(x_1757);
lean_inc(x_1756);
lean_dec(x_1746);
x_1758 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1758, 0, x_1756);
lean_ctor_set(x_1758, 1, x_1757);
return x_1758;
}
}
}
else
{
lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; 
x_1759 = lean_array_get_size(x_23);
x_1760 = l_Array_toSubarray___rarg(x_23, x_27, x_1759);
x_1761 = l_Array_ofSubarray___rarg(x_1760);
lean_dec(x_1760);
if (lean_is_scalar(x_1690)) {
 x_1762 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1762 = x_1690;
}
lean_ctor_set(x_1762, 0, x_1715);
lean_ctor_set(x_1762, 1, x_1761);
x_1763 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1764 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1762, x_1763, x_6, x_7, x_8, x_9, x_1713);
if (lean_obj_tag(x_1764) == 0)
{
lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; 
x_1765 = lean_ctor_get(x_1764, 0);
lean_inc(x_1765);
x_1766 = lean_ctor_get(x_1764, 1);
lean_inc(x_1766);
lean_dec(x_1764);
x_1767 = lean_ctor_get(x_1765, 0);
lean_inc(x_1767);
x_1768 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1767, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1766);
if (lean_obj_tag(x_1768) == 0)
{
lean_object* x_1769; lean_object* x_1770; 
x_1769 = lean_ctor_get(x_1768, 1);
lean_inc(x_1769);
lean_dec(x_1768);
lean_ctor_set(x_1700, 1, x_2);
lean_ctor_set(x_1700, 0, x_1765);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1770 = l_Lean_Compiler_LCNF_Simp_simp(x_1700, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1769);
if (lean_obj_tag(x_1770) == 0)
{
lean_object* x_1771; lean_object* x_1772; 
x_1771 = lean_ctor_get(x_1770, 0);
lean_inc(x_1771);
x_1772 = lean_ctor_get(x_1770, 1);
lean_inc(x_1772);
lean_dec(x_1770);
x_1717 = x_1771;
x_1718 = x_1772;
goto block_1745;
}
else
{
uint8_t x_1773; 
lean_dec(x_1714);
lean_dec(x_1712);
lean_dec(x_1708);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1773 = !lean_is_exclusive(x_1770);
if (x_1773 == 0)
{
return x_1770;
}
else
{
lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; 
x_1774 = lean_ctor_get(x_1770, 0);
x_1775 = lean_ctor_get(x_1770, 1);
lean_inc(x_1775);
lean_inc(x_1774);
lean_dec(x_1770);
x_1776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1776, 0, x_1774);
lean_ctor_set(x_1776, 1, x_1775);
return x_1776;
}
}
}
else
{
uint8_t x_1777; 
lean_dec(x_1765);
lean_dec(x_1714);
lean_dec(x_1712);
lean_dec(x_1708);
lean_free_object(x_1700);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1777 = !lean_is_exclusive(x_1768);
if (x_1777 == 0)
{
return x_1768;
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
x_1778 = lean_ctor_get(x_1768, 0);
x_1779 = lean_ctor_get(x_1768, 1);
lean_inc(x_1779);
lean_inc(x_1778);
lean_dec(x_1768);
x_1780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1780, 0, x_1778);
lean_ctor_set(x_1780, 1, x_1779);
return x_1780;
}
}
}
else
{
uint8_t x_1781; 
lean_dec(x_1714);
lean_dec(x_1712);
lean_dec(x_1708);
lean_free_object(x_1700);
lean_dec(x_1697);
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
x_1781 = !lean_is_exclusive(x_1764);
if (x_1781 == 0)
{
return x_1764;
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; 
x_1782 = lean_ctor_get(x_1764, 0);
x_1783 = lean_ctor_get(x_1764, 1);
lean_inc(x_1783);
lean_inc(x_1782);
lean_dec(x_1764);
x_1784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1784, 0, x_1782);
lean_ctor_set(x_1784, 1, x_1783);
return x_1784;
}
}
}
block_1745:
{
lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1719 = lean_box(0);
if (lean_is_scalar(x_1714)) {
 x_1720 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1720 = x_1714;
 lean_ctor_set_tag(x_1720, 1);
}
lean_ctor_set(x_1720, 0, x_1712);
lean_ctor_set(x_1720, 1, x_1719);
x_1721 = lean_array_mk(x_1720);
x_1722 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_1723 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1721, x_1717, x_1722, x_6, x_7, x_8, x_9, x_1718);
if (lean_obj_tag(x_1723) == 0)
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
x_1724 = lean_ctor_get(x_1723, 0);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1723, 1);
lean_inc(x_1725);
lean_dec(x_1723);
lean_inc(x_1724);
x_1726 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1726, 0, x_1724);
lean_closure_set(x_1726, 1, x_1719);
x_1727 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1697, x_1726, x_6, x_7, x_8, x_9, x_1725);
if (lean_obj_tag(x_1727) == 0)
{
uint8_t x_1728; 
x_1728 = !lean_is_exclusive(x_1727);
if (x_1728 == 0)
{
lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; 
x_1729 = lean_ctor_get(x_1727, 0);
if (lean_is_scalar(x_1708)) {
 x_1730 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1730 = x_1708;
 lean_ctor_set_tag(x_1730, 2);
}
lean_ctor_set(x_1730, 0, x_1724);
lean_ctor_set(x_1730, 1, x_1729);
if (lean_is_scalar(x_22)) {
 x_1731 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1731 = x_22;
}
lean_ctor_set(x_1731, 0, x_1730);
lean_ctor_set(x_1727, 0, x_1731);
return x_1727;
}
else
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; 
x_1732 = lean_ctor_get(x_1727, 0);
x_1733 = lean_ctor_get(x_1727, 1);
lean_inc(x_1733);
lean_inc(x_1732);
lean_dec(x_1727);
if (lean_is_scalar(x_1708)) {
 x_1734 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1734 = x_1708;
 lean_ctor_set_tag(x_1734, 2);
}
lean_ctor_set(x_1734, 0, x_1724);
lean_ctor_set(x_1734, 1, x_1732);
if (lean_is_scalar(x_22)) {
 x_1735 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1735 = x_22;
}
lean_ctor_set(x_1735, 0, x_1734);
x_1736 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1736, 0, x_1735);
lean_ctor_set(x_1736, 1, x_1733);
return x_1736;
}
}
else
{
uint8_t x_1737; 
lean_dec(x_1724);
lean_dec(x_1708);
lean_dec(x_22);
x_1737 = !lean_is_exclusive(x_1727);
if (x_1737 == 0)
{
return x_1727;
}
else
{
lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
x_1738 = lean_ctor_get(x_1727, 0);
x_1739 = lean_ctor_get(x_1727, 1);
lean_inc(x_1739);
lean_inc(x_1738);
lean_dec(x_1727);
x_1740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1740, 0, x_1738);
lean_ctor_set(x_1740, 1, x_1739);
return x_1740;
}
}
}
else
{
uint8_t x_1741; 
lean_dec(x_1708);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1741 = !lean_is_exclusive(x_1723);
if (x_1741 == 0)
{
return x_1723;
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; 
x_1742 = lean_ctor_get(x_1723, 0);
x_1743 = lean_ctor_get(x_1723, 1);
lean_inc(x_1743);
lean_inc(x_1742);
lean_dec(x_1723);
x_1744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1744, 0, x_1742);
lean_ctor_set(x_1744, 1, x_1743);
return x_1744;
}
}
}
}
else
{
lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; 
lean_dec(x_1706);
x_1785 = lean_box(0);
x_1786 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1787 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1788 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1786, x_1697, x_1787, x_6, x_7, x_8, x_9, x_1707);
if (lean_obj_tag(x_1788) == 0)
{
lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; 
x_1789 = lean_ctor_get(x_1788, 0);
lean_inc(x_1789);
x_1790 = lean_ctor_get(x_1788, 1);
lean_inc(x_1790);
lean_dec(x_1788);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1791 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1789, x_6, x_7, x_8, x_9, x_1790);
if (lean_obj_tag(x_1791) == 0)
{
lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; uint8_t x_1795; lean_object* x_1796; lean_object* x_1797; 
x_1792 = lean_ctor_get(x_1791, 0);
lean_inc(x_1792);
x_1793 = lean_ctor_get(x_1791, 1);
lean_inc(x_1793);
lean_dec(x_1791);
x_1794 = lean_ctor_get(x_1792, 0);
lean_inc(x_1794);
x_1795 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1795 == 0)
{
lean_object* x_1810; 
lean_free_object(x_1700);
lean_dec(x_1690);
lean_dec(x_27);
lean_dec(x_23);
x_1810 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1794, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1793);
if (lean_obj_tag(x_1810) == 0)
{
lean_object* x_1811; lean_object* x_1812; 
x_1811 = lean_ctor_get(x_1810, 1);
lean_inc(x_1811);
lean_dec(x_1810);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1812 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1811);
if (lean_obj_tag(x_1812) == 0)
{
lean_object* x_1813; lean_object* x_1814; 
x_1813 = lean_ctor_get(x_1812, 0);
lean_inc(x_1813);
x_1814 = lean_ctor_get(x_1812, 1);
lean_inc(x_1814);
lean_dec(x_1812);
x_1796 = x_1813;
x_1797 = x_1814;
goto block_1809;
}
else
{
uint8_t x_1815; 
lean_dec(x_1792);
lean_dec(x_1708);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1815 = !lean_is_exclusive(x_1812);
if (x_1815 == 0)
{
return x_1812;
}
else
{
lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; 
x_1816 = lean_ctor_get(x_1812, 0);
x_1817 = lean_ctor_get(x_1812, 1);
lean_inc(x_1817);
lean_inc(x_1816);
lean_dec(x_1812);
x_1818 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1818, 0, x_1816);
lean_ctor_set(x_1818, 1, x_1817);
return x_1818;
}
}
}
else
{
uint8_t x_1819; 
lean_dec(x_1792);
lean_dec(x_1708);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1819 = !lean_is_exclusive(x_1810);
if (x_1819 == 0)
{
return x_1810;
}
else
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; 
x_1820 = lean_ctor_get(x_1810, 0);
x_1821 = lean_ctor_get(x_1810, 1);
lean_inc(x_1821);
lean_inc(x_1820);
lean_dec(x_1810);
x_1822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1822, 0, x_1820);
lean_ctor_set(x_1822, 1, x_1821);
return x_1822;
}
}
}
else
{
lean_object* x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; 
x_1823 = lean_array_get_size(x_23);
x_1824 = l_Array_toSubarray___rarg(x_23, x_27, x_1823);
x_1825 = l_Array_ofSubarray___rarg(x_1824);
lean_dec(x_1824);
if (lean_is_scalar(x_1690)) {
 x_1826 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1826 = x_1690;
}
lean_ctor_set(x_1826, 0, x_1794);
lean_ctor_set(x_1826, 1, x_1825);
x_1827 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1828 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1826, x_1827, x_6, x_7, x_8, x_9, x_1793);
if (lean_obj_tag(x_1828) == 0)
{
lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
x_1829 = lean_ctor_get(x_1828, 0);
lean_inc(x_1829);
x_1830 = lean_ctor_get(x_1828, 1);
lean_inc(x_1830);
lean_dec(x_1828);
x_1831 = lean_ctor_get(x_1829, 0);
lean_inc(x_1831);
x_1832 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1831, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1830);
if (lean_obj_tag(x_1832) == 0)
{
lean_object* x_1833; lean_object* x_1834; 
x_1833 = lean_ctor_get(x_1832, 1);
lean_inc(x_1833);
lean_dec(x_1832);
lean_ctor_set(x_1700, 1, x_2);
lean_ctor_set(x_1700, 0, x_1829);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1834 = l_Lean_Compiler_LCNF_Simp_simp(x_1700, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1833);
if (lean_obj_tag(x_1834) == 0)
{
lean_object* x_1835; lean_object* x_1836; 
x_1835 = lean_ctor_get(x_1834, 0);
lean_inc(x_1835);
x_1836 = lean_ctor_get(x_1834, 1);
lean_inc(x_1836);
lean_dec(x_1834);
x_1796 = x_1835;
x_1797 = x_1836;
goto block_1809;
}
else
{
uint8_t x_1837; 
lean_dec(x_1792);
lean_dec(x_1708);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1837 = !lean_is_exclusive(x_1834);
if (x_1837 == 0)
{
return x_1834;
}
else
{
lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; 
x_1838 = lean_ctor_get(x_1834, 0);
x_1839 = lean_ctor_get(x_1834, 1);
lean_inc(x_1839);
lean_inc(x_1838);
lean_dec(x_1834);
x_1840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1840, 0, x_1838);
lean_ctor_set(x_1840, 1, x_1839);
return x_1840;
}
}
}
else
{
uint8_t x_1841; 
lean_dec(x_1829);
lean_dec(x_1792);
lean_dec(x_1708);
lean_free_object(x_1700);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1841 = !lean_is_exclusive(x_1832);
if (x_1841 == 0)
{
return x_1832;
}
else
{
lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; 
x_1842 = lean_ctor_get(x_1832, 0);
x_1843 = lean_ctor_get(x_1832, 1);
lean_inc(x_1843);
lean_inc(x_1842);
lean_dec(x_1832);
x_1844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1844, 0, x_1842);
lean_ctor_set(x_1844, 1, x_1843);
return x_1844;
}
}
}
else
{
uint8_t x_1845; 
lean_dec(x_1792);
lean_dec(x_1708);
lean_free_object(x_1700);
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
x_1845 = !lean_is_exclusive(x_1828);
if (x_1845 == 0)
{
return x_1828;
}
else
{
lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
x_1846 = lean_ctor_get(x_1828, 0);
x_1847 = lean_ctor_get(x_1828, 1);
lean_inc(x_1847);
lean_inc(x_1846);
lean_dec(x_1828);
x_1848 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1848, 0, x_1846);
lean_ctor_set(x_1848, 1, x_1847);
return x_1848;
}
}
}
block_1809:
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; uint8_t x_1802; 
x_1798 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1798, 0, x_1792);
if (lean_is_scalar(x_1708)) {
 x_1799 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1799 = x_1708;
 lean_ctor_set_tag(x_1799, 1);
}
lean_ctor_set(x_1799, 0, x_1798);
lean_ctor_set(x_1799, 1, x_1785);
x_1800 = lean_array_mk(x_1799);
x_1801 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1800, x_1796, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1797);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1800);
x_1802 = !lean_is_exclusive(x_1801);
if (x_1802 == 0)
{
lean_object* x_1803; lean_object* x_1804; 
x_1803 = lean_ctor_get(x_1801, 0);
if (lean_is_scalar(x_22)) {
 x_1804 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1804 = x_22;
}
lean_ctor_set(x_1804, 0, x_1803);
lean_ctor_set(x_1801, 0, x_1804);
return x_1801;
}
else
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
x_1805 = lean_ctor_get(x_1801, 0);
x_1806 = lean_ctor_get(x_1801, 1);
lean_inc(x_1806);
lean_inc(x_1805);
lean_dec(x_1801);
if (lean_is_scalar(x_22)) {
 x_1807 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1807 = x_22;
}
lean_ctor_set(x_1807, 0, x_1805);
x_1808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1808, 0, x_1807);
lean_ctor_set(x_1808, 1, x_1806);
return x_1808;
}
}
}
else
{
uint8_t x_1849; 
lean_dec(x_1708);
lean_free_object(x_1700);
lean_dec(x_1690);
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
x_1849 = !lean_is_exclusive(x_1791);
if (x_1849 == 0)
{
return x_1791;
}
else
{
lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; 
x_1850 = lean_ctor_get(x_1791, 0);
x_1851 = lean_ctor_get(x_1791, 1);
lean_inc(x_1851);
lean_inc(x_1850);
lean_dec(x_1791);
x_1852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1852, 0, x_1850);
lean_ctor_set(x_1852, 1, x_1851);
return x_1852;
}
}
}
else
{
uint8_t x_1853; 
lean_dec(x_1708);
lean_free_object(x_1700);
lean_dec(x_1690);
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
x_1853 = !lean_is_exclusive(x_1788);
if (x_1853 == 0)
{
return x_1788;
}
else
{
lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; 
x_1854 = lean_ctor_get(x_1788, 0);
x_1855 = lean_ctor_get(x_1788, 1);
lean_inc(x_1855);
lean_inc(x_1854);
lean_dec(x_1788);
x_1856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1856, 0, x_1854);
lean_ctor_set(x_1856, 1, x_1855);
return x_1856;
}
}
}
}
else
{
lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; lean_object* x_1863; uint8_t x_1864; 
x_1857 = lean_ctor_get(x_1700, 1);
lean_inc(x_1857);
lean_dec(x_1700);
x_1858 = lean_ctor_get(x_21, 2);
lean_inc(x_1858);
lean_dec(x_21);
x_1859 = l_Lean_Compiler_LCNF_inferAppType(x_1858, x_33, x_6, x_7, x_8, x_9, x_1857);
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
lean_inc(x_1860);
x_1863 = l_Lean_Expr_headBeta(x_1860);
x_1864 = l_Lean_Expr_isForall(x_1863);
lean_dec(x_1863);
if (x_1864 == 0)
{
lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; uint8_t x_1870; lean_object* x_1871; lean_object* x_1872; 
x_1865 = l_Lean_Compiler_LCNF_mkAuxParam(x_1860, x_1691, x_6, x_7, x_8, x_9, x_1861);
x_1866 = lean_ctor_get(x_1865, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1865, 1);
lean_inc(x_1867);
if (lean_is_exclusive(x_1865)) {
 lean_ctor_release(x_1865, 0);
 lean_ctor_release(x_1865, 1);
 x_1868 = x_1865;
} else {
 lean_dec_ref(x_1865);
 x_1868 = lean_box(0);
}
x_1869 = lean_ctor_get(x_1866, 0);
lean_inc(x_1869);
x_1870 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1870 == 0)
{
lean_object* x_1897; 
lean_dec(x_1690);
lean_dec(x_27);
lean_dec(x_23);
x_1897 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1869, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1867);
if (lean_obj_tag(x_1897) == 0)
{
lean_object* x_1898; lean_object* x_1899; 
x_1898 = lean_ctor_get(x_1897, 1);
lean_inc(x_1898);
lean_dec(x_1897);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1899 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1898);
if (lean_obj_tag(x_1899) == 0)
{
lean_object* x_1900; lean_object* x_1901; 
x_1900 = lean_ctor_get(x_1899, 0);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1899, 1);
lean_inc(x_1901);
lean_dec(x_1899);
x_1871 = x_1900;
x_1872 = x_1901;
goto block_1896;
}
else
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
lean_dec(x_1868);
lean_dec(x_1866);
lean_dec(x_1862);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1902 = lean_ctor_get(x_1899, 0);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1899, 1);
lean_inc(x_1903);
if (lean_is_exclusive(x_1899)) {
 lean_ctor_release(x_1899, 0);
 lean_ctor_release(x_1899, 1);
 x_1904 = x_1899;
} else {
 lean_dec_ref(x_1899);
 x_1904 = lean_box(0);
}
if (lean_is_scalar(x_1904)) {
 x_1905 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1905 = x_1904;
}
lean_ctor_set(x_1905, 0, x_1902);
lean_ctor_set(x_1905, 1, x_1903);
return x_1905;
}
}
else
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; 
lean_dec(x_1868);
lean_dec(x_1866);
lean_dec(x_1862);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1906 = lean_ctor_get(x_1897, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1897, 1);
lean_inc(x_1907);
if (lean_is_exclusive(x_1897)) {
 lean_ctor_release(x_1897, 0);
 lean_ctor_release(x_1897, 1);
 x_1908 = x_1897;
} else {
 lean_dec_ref(x_1897);
 x_1908 = lean_box(0);
}
if (lean_is_scalar(x_1908)) {
 x_1909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1909 = x_1908;
}
lean_ctor_set(x_1909, 0, x_1906);
lean_ctor_set(x_1909, 1, x_1907);
return x_1909;
}
}
else
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; 
x_1910 = lean_array_get_size(x_23);
x_1911 = l_Array_toSubarray___rarg(x_23, x_27, x_1910);
x_1912 = l_Array_ofSubarray___rarg(x_1911);
lean_dec(x_1911);
if (lean_is_scalar(x_1690)) {
 x_1913 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1913 = x_1690;
}
lean_ctor_set(x_1913, 0, x_1869);
lean_ctor_set(x_1913, 1, x_1912);
x_1914 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1915 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1913, x_1914, x_6, x_7, x_8, x_9, x_1867);
if (lean_obj_tag(x_1915) == 0)
{
lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; 
x_1916 = lean_ctor_get(x_1915, 0);
lean_inc(x_1916);
x_1917 = lean_ctor_get(x_1915, 1);
lean_inc(x_1917);
lean_dec(x_1915);
x_1918 = lean_ctor_get(x_1916, 0);
lean_inc(x_1918);
x_1919 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1918, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1917);
if (lean_obj_tag(x_1919) == 0)
{
lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; 
x_1920 = lean_ctor_get(x_1919, 1);
lean_inc(x_1920);
lean_dec(x_1919);
x_1921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1921, 0, x_1916);
lean_ctor_set(x_1921, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1922 = l_Lean_Compiler_LCNF_Simp_simp(x_1921, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1920);
if (lean_obj_tag(x_1922) == 0)
{
lean_object* x_1923; lean_object* x_1924; 
x_1923 = lean_ctor_get(x_1922, 0);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1922, 1);
lean_inc(x_1924);
lean_dec(x_1922);
x_1871 = x_1923;
x_1872 = x_1924;
goto block_1896;
}
else
{
lean_object* x_1925; lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; 
lean_dec(x_1868);
lean_dec(x_1866);
lean_dec(x_1862);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1925 = lean_ctor_get(x_1922, 0);
lean_inc(x_1925);
x_1926 = lean_ctor_get(x_1922, 1);
lean_inc(x_1926);
if (lean_is_exclusive(x_1922)) {
 lean_ctor_release(x_1922, 0);
 lean_ctor_release(x_1922, 1);
 x_1927 = x_1922;
} else {
 lean_dec_ref(x_1922);
 x_1927 = lean_box(0);
}
if (lean_is_scalar(x_1927)) {
 x_1928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1928 = x_1927;
}
lean_ctor_set(x_1928, 0, x_1925);
lean_ctor_set(x_1928, 1, x_1926);
return x_1928;
}
}
else
{
lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; 
lean_dec(x_1916);
lean_dec(x_1868);
lean_dec(x_1866);
lean_dec(x_1862);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1929 = lean_ctor_get(x_1919, 0);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1919, 1);
lean_inc(x_1930);
if (lean_is_exclusive(x_1919)) {
 lean_ctor_release(x_1919, 0);
 lean_ctor_release(x_1919, 1);
 x_1931 = x_1919;
} else {
 lean_dec_ref(x_1919);
 x_1931 = lean_box(0);
}
if (lean_is_scalar(x_1931)) {
 x_1932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1932 = x_1931;
}
lean_ctor_set(x_1932, 0, x_1929);
lean_ctor_set(x_1932, 1, x_1930);
return x_1932;
}
}
else
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; 
lean_dec(x_1868);
lean_dec(x_1866);
lean_dec(x_1862);
lean_dec(x_1697);
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
x_1933 = lean_ctor_get(x_1915, 0);
lean_inc(x_1933);
x_1934 = lean_ctor_get(x_1915, 1);
lean_inc(x_1934);
if (lean_is_exclusive(x_1915)) {
 lean_ctor_release(x_1915, 0);
 lean_ctor_release(x_1915, 1);
 x_1935 = x_1915;
} else {
 lean_dec_ref(x_1915);
 x_1935 = lean_box(0);
}
if (lean_is_scalar(x_1935)) {
 x_1936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1936 = x_1935;
}
lean_ctor_set(x_1936, 0, x_1933);
lean_ctor_set(x_1936, 1, x_1934);
return x_1936;
}
}
block_1896:
{
lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; 
x_1873 = lean_box(0);
if (lean_is_scalar(x_1868)) {
 x_1874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1874 = x_1868;
 lean_ctor_set_tag(x_1874, 1);
}
lean_ctor_set(x_1874, 0, x_1866);
lean_ctor_set(x_1874, 1, x_1873);
x_1875 = lean_array_mk(x_1874);
x_1876 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__2;
x_1877 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1875, x_1871, x_1876, x_6, x_7, x_8, x_9, x_1872);
if (lean_obj_tag(x_1877) == 0)
{
lean_object* x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; 
x_1878 = lean_ctor_get(x_1877, 0);
lean_inc(x_1878);
x_1879 = lean_ctor_get(x_1877, 1);
lean_inc(x_1879);
lean_dec(x_1877);
lean_inc(x_1878);
x_1880 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__1___boxed), 8, 2);
lean_closure_set(x_1880, 0, x_1878);
lean_closure_set(x_1880, 1, x_1873);
x_1881 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1697, x_1880, x_6, x_7, x_8, x_9, x_1879);
if (lean_obj_tag(x_1881) == 0)
{
lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; 
x_1882 = lean_ctor_get(x_1881, 0);
lean_inc(x_1882);
x_1883 = lean_ctor_get(x_1881, 1);
lean_inc(x_1883);
if (lean_is_exclusive(x_1881)) {
 lean_ctor_release(x_1881, 0);
 lean_ctor_release(x_1881, 1);
 x_1884 = x_1881;
} else {
 lean_dec_ref(x_1881);
 x_1884 = lean_box(0);
}
if (lean_is_scalar(x_1862)) {
 x_1885 = lean_alloc_ctor(2, 2, 0);
} else {
 x_1885 = x_1862;
 lean_ctor_set_tag(x_1885, 2);
}
lean_ctor_set(x_1885, 0, x_1878);
lean_ctor_set(x_1885, 1, x_1882);
if (lean_is_scalar(x_22)) {
 x_1886 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1886 = x_22;
}
lean_ctor_set(x_1886, 0, x_1885);
if (lean_is_scalar(x_1884)) {
 x_1887 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1887 = x_1884;
}
lean_ctor_set(x_1887, 0, x_1886);
lean_ctor_set(x_1887, 1, x_1883);
return x_1887;
}
else
{
lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; 
lean_dec(x_1878);
lean_dec(x_1862);
lean_dec(x_22);
x_1888 = lean_ctor_get(x_1881, 0);
lean_inc(x_1888);
x_1889 = lean_ctor_get(x_1881, 1);
lean_inc(x_1889);
if (lean_is_exclusive(x_1881)) {
 lean_ctor_release(x_1881, 0);
 lean_ctor_release(x_1881, 1);
 x_1890 = x_1881;
} else {
 lean_dec_ref(x_1881);
 x_1890 = lean_box(0);
}
if (lean_is_scalar(x_1890)) {
 x_1891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1891 = x_1890;
}
lean_ctor_set(x_1891, 0, x_1888);
lean_ctor_set(x_1891, 1, x_1889);
return x_1891;
}
}
else
{
lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; 
lean_dec(x_1862);
lean_dec(x_1697);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_1892 = lean_ctor_get(x_1877, 0);
lean_inc(x_1892);
x_1893 = lean_ctor_get(x_1877, 1);
lean_inc(x_1893);
if (lean_is_exclusive(x_1877)) {
 lean_ctor_release(x_1877, 0);
 lean_ctor_release(x_1877, 1);
 x_1894 = x_1877;
} else {
 lean_dec_ref(x_1877);
 x_1894 = lean_box(0);
}
if (lean_is_scalar(x_1894)) {
 x_1895 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1895 = x_1894;
}
lean_ctor_set(x_1895, 0, x_1892);
lean_ctor_set(x_1895, 1, x_1893);
return x_1895;
}
}
}
else
{
lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; 
lean_dec(x_1860);
x_1937 = lean_box(0);
x_1938 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
x_1939 = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6;
x_1940 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1938, x_1697, x_1939, x_6, x_7, x_8, x_9, x_1861);
if (lean_obj_tag(x_1940) == 0)
{
lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; 
x_1941 = lean_ctor_get(x_1940, 0);
lean_inc(x_1941);
x_1942 = lean_ctor_get(x_1940, 1);
lean_inc(x_1942);
lean_dec(x_1940);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1943 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_1941, x_6, x_7, x_8, x_9, x_1942);
if (lean_obj_tag(x_1943) == 0)
{
lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; uint8_t x_1947; lean_object* x_1948; lean_object* x_1949; 
x_1944 = lean_ctor_get(x_1943, 0);
lean_inc(x_1944);
x_1945 = lean_ctor_get(x_1943, 1);
lean_inc(x_1945);
lean_dec(x_1943);
x_1946 = lean_ctor_get(x_1944, 0);
lean_inc(x_1946);
x_1947 = lean_nat_dec_lt(x_27, x_24);
lean_dec(x_24);
if (x_1947 == 0)
{
lean_object* x_1960; 
lean_dec(x_1690);
lean_dec(x_27);
lean_dec(x_23);
x_1960 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1946, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1945);
if (lean_obj_tag(x_1960) == 0)
{
lean_object* x_1961; lean_object* x_1962; 
x_1961 = lean_ctor_get(x_1960, 1);
lean_inc(x_1961);
lean_dec(x_1960);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1962 = l_Lean_Compiler_LCNF_Simp_simp(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1961);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; lean_object* x_1964; 
x_1963 = lean_ctor_get(x_1962, 0);
lean_inc(x_1963);
x_1964 = lean_ctor_get(x_1962, 1);
lean_inc(x_1964);
lean_dec(x_1962);
x_1948 = x_1963;
x_1949 = x_1964;
goto block_1959;
}
else
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; 
lean_dec(x_1944);
lean_dec(x_1862);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_1944);
lean_dec(x_1862);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1969 = lean_ctor_get(x_1960, 0);
lean_inc(x_1969);
x_1970 = lean_ctor_get(x_1960, 1);
lean_inc(x_1970);
if (lean_is_exclusive(x_1960)) {
 lean_ctor_release(x_1960, 0);
 lean_ctor_release(x_1960, 1);
 x_1971 = x_1960;
} else {
 lean_dec_ref(x_1960);
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
lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; 
x_1973 = lean_array_get_size(x_23);
x_1974 = l_Array_toSubarray___rarg(x_23, x_27, x_1973);
x_1975 = l_Array_ofSubarray___rarg(x_1974);
lean_dec(x_1974);
if (lean_is_scalar(x_1690)) {
 x_1976 = lean_alloc_ctor(4, 2, 0);
} else {
 x_1976 = x_1690;
}
lean_ctor_set(x_1976, 0, x_1946);
lean_ctor_set(x_1976, 1, x_1975);
x_1977 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_1978 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_1976, x_1977, x_6, x_7, x_8, x_9, x_1945);
if (lean_obj_tag(x_1978) == 0)
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; 
x_1979 = lean_ctor_get(x_1978, 0);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1978, 1);
lean_inc(x_1980);
lean_dec(x_1978);
x_1981 = lean_ctor_get(x_1979, 0);
lean_inc(x_1981);
x_1982 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_1981, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1980);
if (lean_obj_tag(x_1982) == 0)
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
x_1983 = lean_ctor_get(x_1982, 1);
lean_inc(x_1983);
lean_dec(x_1982);
x_1984 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1984, 0, x_1979);
lean_ctor_set(x_1984, 1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_1985 = l_Lean_Compiler_LCNF_Simp_simp(x_1984, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1983);
if (lean_obj_tag(x_1985) == 0)
{
lean_object* x_1986; lean_object* x_1987; 
x_1986 = lean_ctor_get(x_1985, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1985, 1);
lean_inc(x_1987);
lean_dec(x_1985);
x_1948 = x_1986;
x_1949 = x_1987;
goto block_1959;
}
else
{
lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; 
lean_dec(x_1944);
lean_dec(x_1862);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_1988 = lean_ctor_get(x_1985, 0);
lean_inc(x_1988);
x_1989 = lean_ctor_get(x_1985, 1);
lean_inc(x_1989);
if (lean_is_exclusive(x_1985)) {
 lean_ctor_release(x_1985, 0);
 lean_ctor_release(x_1985, 1);
 x_1990 = x_1985;
} else {
 lean_dec_ref(x_1985);
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
lean_dec(x_1979);
lean_dec(x_1944);
lean_dec(x_1862);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_1992 = lean_ctor_get(x_1982, 0);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1982, 1);
lean_inc(x_1993);
if (lean_is_exclusive(x_1982)) {
 lean_ctor_release(x_1982, 0);
 lean_ctor_release(x_1982, 1);
 x_1994 = x_1982;
} else {
 lean_dec_ref(x_1982);
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
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; 
lean_dec(x_1944);
lean_dec(x_1862);
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
x_1996 = lean_ctor_get(x_1978, 0);
lean_inc(x_1996);
x_1997 = lean_ctor_get(x_1978, 1);
lean_inc(x_1997);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1998 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1998 = lean_box(0);
}
if (lean_is_scalar(x_1998)) {
 x_1999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1999 = x_1998;
}
lean_ctor_set(x_1999, 0, x_1996);
lean_ctor_set(x_1999, 1, x_1997);
return x_1999;
}
}
block_1959:
{
lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; 
x_1950 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1950, 0, x_1944);
if (lean_is_scalar(x_1862)) {
 x_1951 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1951 = x_1862;
 lean_ctor_set_tag(x_1951, 1);
}
lean_ctor_set(x_1951, 0, x_1950);
lean_ctor_set(x_1951, 1, x_1937);
x_1952 = lean_array_mk(x_1951);
x_1953 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_1952, x_1948, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_1949);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1952);
x_1954 = lean_ctor_get(x_1953, 0);
lean_inc(x_1954);
x_1955 = lean_ctor_get(x_1953, 1);
lean_inc(x_1955);
if (lean_is_exclusive(x_1953)) {
 lean_ctor_release(x_1953, 0);
 lean_ctor_release(x_1953, 1);
 x_1956 = x_1953;
} else {
 lean_dec_ref(x_1953);
 x_1956 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_1957 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1957 = x_22;
}
lean_ctor_set(x_1957, 0, x_1954);
if (lean_is_scalar(x_1956)) {
 x_1958 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1958 = x_1956;
}
lean_ctor_set(x_1958, 0, x_1957);
lean_ctor_set(x_1958, 1, x_1955);
return x_1958;
}
}
else
{
lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; 
lean_dec(x_1862);
lean_dec(x_1690);
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
x_2000 = lean_ctor_get(x_1943, 0);
lean_inc(x_2000);
x_2001 = lean_ctor_get(x_1943, 1);
lean_inc(x_2001);
if (lean_is_exclusive(x_1943)) {
 lean_ctor_release(x_1943, 0);
 lean_ctor_release(x_1943, 1);
 x_2002 = x_1943;
} else {
 lean_dec_ref(x_1943);
 x_2002 = lean_box(0);
}
if (lean_is_scalar(x_2002)) {
 x_2003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2003 = x_2002;
}
lean_ctor_set(x_2003, 0, x_2000);
lean_ctor_set(x_2003, 1, x_2001);
return x_2003;
}
}
else
{
lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; 
lean_dec(x_1862);
lean_dec(x_1690);
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
x_2004 = lean_ctor_get(x_1940, 0);
lean_inc(x_2004);
x_2005 = lean_ctor_get(x_1940, 1);
lean_inc(x_2005);
if (lean_is_exclusive(x_1940)) {
 lean_ctor_release(x_1940, 0);
 lean_ctor_release(x_1940, 1);
 x_2006 = x_1940;
} else {
 lean_dec_ref(x_1940);
 x_2006 = lean_box(0);
}
if (lean_is_scalar(x_2006)) {
 x_2007 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2007 = x_2006;
}
lean_ctor_set(x_2007, 0, x_2004);
lean_ctor_set(x_2007, 1, x_2005);
return x_2007;
}
}
}
}
else
{
lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; lean_object* x_2011; 
lean_dec(x_1690);
lean_dec(x_33);
lean_dec(x_21);
x_2008 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_1698);
x_2009 = lean_ctor_get(x_2008, 1);
lean_inc(x_2009);
lean_dec(x_2008);
x_2010 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed), 14, 8);
lean_closure_set(x_2010, 0, x_3);
lean_closure_set(x_2010, 1, x_4);
lean_closure_set(x_2010, 2, x_5);
lean_closure_set(x_2010, 3, x_27);
lean_closure_set(x_2010, 4, x_24);
lean_closure_set(x_2010, 5, x_26);
lean_closure_set(x_2010, 6, x_2);
lean_closure_set(x_2010, 7, x_23);
x_2011 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_1697, x_2010, x_6, x_7, x_8, x_9, x_2009);
if (lean_obj_tag(x_2011) == 0)
{
uint8_t x_2012; 
x_2012 = !lean_is_exclusive(x_2011);
if (x_2012 == 0)
{
lean_object* x_2013; lean_object* x_2014; 
x_2013 = lean_ctor_get(x_2011, 0);
if (lean_is_scalar(x_22)) {
 x_2014 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2014 = x_22;
}
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
if (lean_is_scalar(x_22)) {
 x_2017 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2017 = x_22;
}
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
lean_dec(x_22);
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
else
{
uint8_t x_2023; 
lean_dec(x_1690);
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
x_2023 = !lean_is_exclusive(x_1696);
if (x_2023 == 0)
{
return x_1696;
}
else
{
lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; 
x_2024 = lean_ctor_get(x_1696, 0);
x_2025 = lean_ctor_get(x_1696, 1);
lean_inc(x_2025);
lean_inc(x_2024);
lean_dec(x_1696);
x_2026 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2026, 0, x_2024);
lean_ctor_set(x_2026, 1, x_2025);
return x_2026;
}
}
}
}
else
{
uint8_t x_2046; 
lean_dec(x_1690);
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
x_2046 = !lean_is_exclusive(x_1692);
if (x_2046 == 0)
{
return x_1692;
}
else
{
lean_object* x_2047; lean_object* x_2048; lean_object* x_2049; 
x_2047 = lean_ctor_get(x_1692, 0);
x_2048 = lean_ctor_get(x_1692, 1);
lean_inc(x_2048);
lean_inc(x_2047);
lean_dec(x_1692);
x_2049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2049, 0, x_2047);
lean_ctor_set(x_2049, 1, x_2048);
return x_2049;
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
lean_object* x_2050; lean_object* x_2051; 
x_2050 = lean_ctor_get(x_11, 0);
lean_inc(x_2050);
lean_dec(x_11);
lean_inc(x_3);
lean_inc(x_2050);
x_2051 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_25, x_2050, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2051) == 0)
{
lean_object* x_2052; lean_object* x_2053; uint8_t x_2054; 
x_2052 = lean_ctor_get(x_2051, 0);
lean_inc(x_2052);
x_2053 = lean_ctor_get(x_2051, 1);
lean_inc(x_2053);
lean_dec(x_2051);
x_2054 = !lean_is_exclusive(x_3);
if (x_2054 == 0)
{
lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; 
x_2055 = lean_ctor_get(x_3, 2);
x_2056 = lean_ctor_get(x_3, 3);
lean_inc(x_2050);
x_2057 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2057, 0, x_2050);
lean_ctor_set(x_2057, 1, x_2055);
x_2058 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_2056, x_2050, x_2052);
lean_ctor_set(x_3, 3, x_2058);
lean_ctor_set(x_3, 2, x_2057);
x_2059 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2053);
if (lean_obj_tag(x_2059) == 0)
{
lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; 
x_2060 = lean_ctor_get(x_2059, 0);
lean_inc(x_2060);
x_2061 = lean_ctor_get(x_2059, 1);
lean_inc(x_2061);
lean_dec(x_2059);
x_2062 = lean_ctor_get(x_2060, 0);
lean_inc(x_2062);
x_2063 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2062, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2061);
if (lean_obj_tag(x_2063) == 0)
{
lean_object* x_2064; lean_object* x_2065; uint8_t x_2066; 
x_2064 = lean_ctor_get(x_2063, 1);
lean_inc(x_2064);
lean_dec(x_2063);
x_2065 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2064);
x_2066 = !lean_is_exclusive(x_2065);
if (x_2066 == 0)
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; 
x_2067 = lean_ctor_get(x_2065, 1);
x_2068 = lean_ctor_get(x_2065, 0);
lean_dec(x_2068);
lean_ctor_set_tag(x_2065, 1);
lean_ctor_set(x_2065, 1, x_2);
lean_ctor_set(x_2065, 0, x_2060);
x_2069 = l_Lean_Compiler_LCNF_Simp_simp(x_2065, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2067);
if (lean_obj_tag(x_2069) == 0)
{
uint8_t x_2070; 
x_2070 = !lean_is_exclusive(x_2069);
if (x_2070 == 0)
{
lean_object* x_2071; lean_object* x_2072; 
x_2071 = lean_ctor_get(x_2069, 0);
if (lean_is_scalar(x_22)) {
 x_2072 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2072 = x_22;
}
lean_ctor_set(x_2072, 0, x_2071);
lean_ctor_set(x_2069, 0, x_2072);
return x_2069;
}
else
{
lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; 
x_2073 = lean_ctor_get(x_2069, 0);
x_2074 = lean_ctor_get(x_2069, 1);
lean_inc(x_2074);
lean_inc(x_2073);
lean_dec(x_2069);
if (lean_is_scalar(x_22)) {
 x_2075 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2075 = x_22;
}
lean_ctor_set(x_2075, 0, x_2073);
x_2076 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2076, 0, x_2075);
lean_ctor_set(x_2076, 1, x_2074);
return x_2076;
}
}
else
{
uint8_t x_2077; 
lean_dec(x_22);
x_2077 = !lean_is_exclusive(x_2069);
if (x_2077 == 0)
{
return x_2069;
}
else
{
lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; 
x_2078 = lean_ctor_get(x_2069, 0);
x_2079 = lean_ctor_get(x_2069, 1);
lean_inc(x_2079);
lean_inc(x_2078);
lean_dec(x_2069);
x_2080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2080, 0, x_2078);
lean_ctor_set(x_2080, 1, x_2079);
return x_2080;
}
}
}
else
{
lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; 
x_2081 = lean_ctor_get(x_2065, 1);
lean_inc(x_2081);
lean_dec(x_2065);
x_2082 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2082, 0, x_2060);
lean_ctor_set(x_2082, 1, x_2);
x_2083 = l_Lean_Compiler_LCNF_Simp_simp(x_2082, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2081);
if (lean_obj_tag(x_2083) == 0)
{
lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; 
x_2084 = lean_ctor_get(x_2083, 0);
lean_inc(x_2084);
x_2085 = lean_ctor_get(x_2083, 1);
lean_inc(x_2085);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2086 = x_2083;
} else {
 lean_dec_ref(x_2083);
 x_2086 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2087 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2087 = x_22;
}
lean_ctor_set(x_2087, 0, x_2084);
if (lean_is_scalar(x_2086)) {
 x_2088 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2088 = x_2086;
}
lean_ctor_set(x_2088, 0, x_2087);
lean_ctor_set(x_2088, 1, x_2085);
return x_2088;
}
else
{
lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
lean_dec(x_22);
x_2089 = lean_ctor_get(x_2083, 0);
lean_inc(x_2089);
x_2090 = lean_ctor_get(x_2083, 1);
lean_inc(x_2090);
if (lean_is_exclusive(x_2083)) {
 lean_ctor_release(x_2083, 0);
 lean_ctor_release(x_2083, 1);
 x_2091 = x_2083;
} else {
 lean_dec_ref(x_2083);
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
}
else
{
uint8_t x_2093; 
lean_dec(x_2060);
lean_dec(x_3);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2093 = !lean_is_exclusive(x_2063);
if (x_2093 == 0)
{
return x_2063;
}
else
{
lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
x_2094 = lean_ctor_get(x_2063, 0);
x_2095 = lean_ctor_get(x_2063, 1);
lean_inc(x_2095);
lean_inc(x_2094);
lean_dec(x_2063);
x_2096 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2096, 0, x_2094);
lean_ctor_set(x_2096, 1, x_2095);
return x_2096;
}
}
}
else
{
uint8_t x_2097; 
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
x_2097 = !lean_is_exclusive(x_2059);
if (x_2097 == 0)
{
return x_2059;
}
else
{
lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; 
x_2098 = lean_ctor_get(x_2059, 0);
x_2099 = lean_ctor_get(x_2059, 1);
lean_inc(x_2099);
lean_inc(x_2098);
lean_dec(x_2059);
x_2100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2100, 0, x_2098);
lean_ctor_set(x_2100, 1, x_2099);
return x_2100;
}
}
}
else
{
lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; 
x_2101 = lean_ctor_get(x_3, 0);
x_2102 = lean_ctor_get(x_3, 1);
x_2103 = lean_ctor_get(x_3, 2);
x_2104 = lean_ctor_get(x_3, 3);
lean_inc(x_2104);
lean_inc(x_2103);
lean_inc(x_2102);
lean_inc(x_2101);
lean_dec(x_3);
lean_inc(x_2050);
x_2105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2105, 0, x_2050);
lean_ctor_set(x_2105, 1, x_2103);
x_2106 = l_Lean_PersistentHashMap_insert___at_Lean_Kernel_Environment_Diagnostics_recordUnfold___spec__4(x_2104, x_2050, x_2052);
x_2107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2107, 0, x_2101);
lean_ctor_set(x_2107, 1, x_2102);
lean_ctor_set(x_2107, 2, x_2105);
lean_ctor_set(x_2107, 3, x_2106);
x_2108 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_2107, x_4, x_5, x_6, x_7, x_8, x_9, x_2053);
if (lean_obj_tag(x_2108) == 0)
{
lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; 
x_2109 = lean_ctor_get(x_2108, 0);
lean_inc(x_2109);
x_2110 = lean_ctor_get(x_2108, 1);
lean_inc(x_2110);
lean_dec(x_2108);
x_2111 = lean_ctor_get(x_2109, 0);
lean_inc(x_2111);
x_2112 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2111, x_2107, x_4, x_5, x_6, x_7, x_8, x_9, x_2110);
if (lean_obj_tag(x_2112) == 0)
{
lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; 
x_2113 = lean_ctor_get(x_2112, 1);
lean_inc(x_2113);
lean_dec(x_2112);
x_2114 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2113);
x_2115 = lean_ctor_get(x_2114, 1);
lean_inc(x_2115);
if (lean_is_exclusive(x_2114)) {
 lean_ctor_release(x_2114, 0);
 lean_ctor_release(x_2114, 1);
 x_2116 = x_2114;
} else {
 lean_dec_ref(x_2114);
 x_2116 = lean_box(0);
}
if (lean_is_scalar(x_2116)) {
 x_2117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2117 = x_2116;
 lean_ctor_set_tag(x_2117, 1);
}
lean_ctor_set(x_2117, 0, x_2109);
lean_ctor_set(x_2117, 1, x_2);
x_2118 = l_Lean_Compiler_LCNF_Simp_simp(x_2117, x_2107, x_4, x_5, x_6, x_7, x_8, x_9, x_2115);
if (lean_obj_tag(x_2118) == 0)
{
lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; 
x_2119 = lean_ctor_get(x_2118, 0);
lean_inc(x_2119);
x_2120 = lean_ctor_get(x_2118, 1);
lean_inc(x_2120);
if (lean_is_exclusive(x_2118)) {
 lean_ctor_release(x_2118, 0);
 lean_ctor_release(x_2118, 1);
 x_2121 = x_2118;
} else {
 lean_dec_ref(x_2118);
 x_2121 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2122 = x_22;
}
lean_ctor_set(x_2122, 0, x_2119);
if (lean_is_scalar(x_2121)) {
 x_2123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2123 = x_2121;
}
lean_ctor_set(x_2123, 0, x_2122);
lean_ctor_set(x_2123, 1, x_2120);
return x_2123;
}
else
{
lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; 
lean_dec(x_22);
x_2124 = lean_ctor_get(x_2118, 0);
lean_inc(x_2124);
x_2125 = lean_ctor_get(x_2118, 1);
lean_inc(x_2125);
if (lean_is_exclusive(x_2118)) {
 lean_ctor_release(x_2118, 0);
 lean_ctor_release(x_2118, 1);
 x_2126 = x_2118;
} else {
 lean_dec_ref(x_2118);
 x_2126 = lean_box(0);
}
if (lean_is_scalar(x_2126)) {
 x_2127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2127 = x_2126;
}
lean_ctor_set(x_2127, 0, x_2124);
lean_ctor_set(x_2127, 1, x_2125);
return x_2127;
}
}
else
{
lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; lean_object* x_2131; 
lean_dec(x_2109);
lean_dec(x_2107);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2128 = lean_ctor_get(x_2112, 0);
lean_inc(x_2128);
x_2129 = lean_ctor_get(x_2112, 1);
lean_inc(x_2129);
if (lean_is_exclusive(x_2112)) {
 lean_ctor_release(x_2112, 0);
 lean_ctor_release(x_2112, 1);
 x_2130 = x_2112;
} else {
 lean_dec_ref(x_2112);
 x_2130 = lean_box(0);
}
if (lean_is_scalar(x_2130)) {
 x_2131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2131 = x_2130;
}
lean_ctor_set(x_2131, 0, x_2128);
lean_ctor_set(x_2131, 1, x_2129);
return x_2131;
}
}
else
{
lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; 
lean_dec(x_2107);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_2132 = lean_ctor_get(x_2108, 0);
lean_inc(x_2132);
x_2133 = lean_ctor_get(x_2108, 1);
lean_inc(x_2133);
if (lean_is_exclusive(x_2108)) {
 lean_ctor_release(x_2108, 0);
 lean_ctor_release(x_2108, 1);
 x_2134 = x_2108;
} else {
 lean_dec_ref(x_2108);
 x_2134 = lean_box(0);
}
if (lean_is_scalar(x_2134)) {
 x_2135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2135 = x_2134;
}
lean_ctor_set(x_2135, 0, x_2132);
lean_ctor_set(x_2135, 1, x_2133);
return x_2135;
}
}
}
else
{
uint8_t x_2136; 
lean_dec(x_2050);
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
x_2136 = !lean_is_exclusive(x_2051);
if (x_2136 == 0)
{
return x_2051;
}
else
{
lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; 
x_2137 = lean_ctor_get(x_2051, 0);
x_2138 = lean_ctor_get(x_2051, 1);
lean_inc(x_2138);
lean_inc(x_2137);
lean_dec(x_2051);
x_2139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2139, 0, x_2137);
lean_ctor_set(x_2139, 1, x_2138);
return x_2139;
}
}
}
else
{
lean_object* x_2140; 
lean_dec(x_11);
x_2140 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_2140) == 0)
{
lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2141 = lean_ctor_get(x_2140, 0);
lean_inc(x_2141);
x_2142 = lean_ctor_get(x_2140, 1);
lean_inc(x_2142);
lean_dec(x_2140);
x_2143 = lean_ctor_get(x_2141, 0);
lean_inc(x_2143);
x_2144 = l_Lean_Compiler_LCNF_Simp_addFVarSubst(x_26, x_2143, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2142);
if (lean_obj_tag(x_2144) == 0)
{
lean_object* x_2145; lean_object* x_2146; uint8_t x_2147; 
x_2145 = lean_ctor_get(x_2144, 1);
lean_inc(x_2145);
lean_dec(x_2144);
x_2146 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_2145);
x_2147 = !lean_is_exclusive(x_2146);
if (x_2147 == 0)
{
lean_object* x_2148; lean_object* x_2149; lean_object* x_2150; 
x_2148 = lean_ctor_get(x_2146, 1);
x_2149 = lean_ctor_get(x_2146, 0);
lean_dec(x_2149);
lean_ctor_set_tag(x_2146, 1);
lean_ctor_set(x_2146, 1, x_2);
lean_ctor_set(x_2146, 0, x_2141);
x_2150 = l_Lean_Compiler_LCNF_Simp_simp(x_2146, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2148);
if (lean_obj_tag(x_2150) == 0)
{
uint8_t x_2151; 
x_2151 = !lean_is_exclusive(x_2150);
if (x_2151 == 0)
{
lean_object* x_2152; lean_object* x_2153; 
x_2152 = lean_ctor_get(x_2150, 0);
if (lean_is_scalar(x_22)) {
 x_2153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2153 = x_22;
}
lean_ctor_set(x_2153, 0, x_2152);
lean_ctor_set(x_2150, 0, x_2153);
return x_2150;
}
else
{
lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; 
x_2154 = lean_ctor_get(x_2150, 0);
x_2155 = lean_ctor_get(x_2150, 1);
lean_inc(x_2155);
lean_inc(x_2154);
lean_dec(x_2150);
if (lean_is_scalar(x_22)) {
 x_2156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2156 = x_22;
}
lean_ctor_set(x_2156, 0, x_2154);
x_2157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2157, 0, x_2156);
lean_ctor_set(x_2157, 1, x_2155);
return x_2157;
}
}
else
{
uint8_t x_2158; 
lean_dec(x_22);
x_2158 = !lean_is_exclusive(x_2150);
if (x_2158 == 0)
{
return x_2150;
}
else
{
lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
x_2159 = lean_ctor_get(x_2150, 0);
x_2160 = lean_ctor_get(x_2150, 1);
lean_inc(x_2160);
lean_inc(x_2159);
lean_dec(x_2150);
x_2161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2161, 0, x_2159);
lean_ctor_set(x_2161, 1, x_2160);
return x_2161;
}
}
}
else
{
lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; 
x_2162 = lean_ctor_get(x_2146, 1);
lean_inc(x_2162);
lean_dec(x_2146);
x_2163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2163, 0, x_2141);
lean_ctor_set(x_2163, 1, x_2);
x_2164 = l_Lean_Compiler_LCNF_Simp_simp(x_2163, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2162);
if (lean_obj_tag(x_2164) == 0)
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; 
x_2165 = lean_ctor_get(x_2164, 0);
lean_inc(x_2165);
x_2166 = lean_ctor_get(x_2164, 1);
lean_inc(x_2166);
if (lean_is_exclusive(x_2164)) {
 lean_ctor_release(x_2164, 0);
 lean_ctor_release(x_2164, 1);
 x_2167 = x_2164;
} else {
 lean_dec_ref(x_2164);
 x_2167 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_2168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2168 = x_22;
}
lean_ctor_set(x_2168, 0, x_2165);
if (lean_is_scalar(x_2167)) {
 x_2169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2169 = x_2167;
}
lean_ctor_set(x_2169, 0, x_2168);
lean_ctor_set(x_2169, 1, x_2166);
return x_2169;
}
else
{
lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; 
lean_dec(x_22);
x_2170 = lean_ctor_get(x_2164, 0);
lean_inc(x_2170);
x_2171 = lean_ctor_get(x_2164, 1);
lean_inc(x_2171);
if (lean_is_exclusive(x_2164)) {
 lean_ctor_release(x_2164, 0);
 lean_ctor_release(x_2164, 1);
 x_2172 = x_2164;
} else {
 lean_dec_ref(x_2164);
 x_2172 = lean_box(0);
}
if (lean_is_scalar(x_2172)) {
 x_2173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2173 = x_2172;
}
lean_ctor_set(x_2173, 0, x_2170);
lean_ctor_set(x_2173, 1, x_2171);
return x_2173;
}
}
}
else
{
uint8_t x_2174; 
lean_dec(x_2141);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_2174 = !lean_is_exclusive(x_2144);
if (x_2174 == 0)
{
return x_2144;
}
else
{
lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; 
x_2175 = lean_ctor_get(x_2144, 0);
x_2176 = lean_ctor_get(x_2144, 1);
lean_inc(x_2176);
lean_inc(x_2175);
lean_dec(x_2144);
x_2177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2177, 0, x_2175);
lean_ctor_set(x_2177, 1, x_2176);
return x_2177;
}
}
}
else
{
uint8_t x_2178; 
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
x_2178 = !lean_is_exclusive(x_2140);
if (x_2178 == 0)
{
return x_2140;
}
else
{
lean_object* x_2179; lean_object* x_2180; lean_object* x_2181; 
x_2179 = lean_ctor_get(x_2140, 0);
x_2180 = lean_ctor_get(x_2140, 1);
lean_inc(x_2180);
lean_inc(x_2179);
lean_dec(x_2140);
x_2181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2181, 0, x_2179);
lean_ctor_set(x_2181, 1, x_2180);
return x_2181;
}
}
}
}
}
}
else
{
uint8_t x_2182; 
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
x_2182 = !lean_is_exclusive(x_12);
if (x_2182 == 0)
{
return x_12;
}
else
{
lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; 
x_2183 = lean_ctor_get(x_12, 0);
x_2184 = lean_ctor_get(x_12, 1);
lean_inc(x_2184);
lean_inc(x_2183);
lean_dec(x_12);
x_2185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2185, 0, x_2183);
lean_ctor_set(x_2185, 1, x_2184);
return x_2185;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_48 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(x_42, x_46);
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
x_389 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(x_383, x_387);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_17 = lean_array_uget(x_3, x_5);
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 2);
lean_inc(x_29);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_17);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_6);
x_18 = x_31;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_33 = lean_ctor_get(x_6, 2);
lean_dec(x_33);
x_34 = lean_ctor_get(x_6, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_6, 0);
lean_dec(x_35);
x_36 = lean_array_fget(x_27, x_28);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_28, x_37);
lean_dec(x_28);
lean_ctor_set(x_6, 1, x_38);
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = l_Lean_Compiler_LCNF_Arg_toExpr(x_36);
x_41 = lean_st_ref_take(x_8, x_14);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; size_t x_58; size_t x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
x_50 = lean_array_get_size(x_49);
x_51 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_39);
x_52 = 32;
x_53 = lean_uint64_shift_right(x_51, x_52);
x_54 = lean_uint64_xor(x_51, x_53);
x_55 = 16;
x_56 = lean_uint64_shift_right(x_54, x_55);
x_57 = lean_uint64_xor(x_54, x_56);
x_58 = lean_uint64_to_usize(x_57);
x_59 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_60 = 1;
x_61 = lean_usize_sub(x_59, x_60);
x_62 = lean_usize_land(x_58, x_61);
x_63 = lean_array_uget(x_49, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_39, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_65 = lean_nat_add(x_48, x_37);
lean_dec(x_48);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_39);
lean_ctor_set(x_66, 1, x_40);
lean_ctor_set(x_66, 2, x_63);
x_67 = lean_array_uset(x_49, x_62, x_66);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_mul(x_65, x_68);
x_70 = lean_unsigned_to_nat(3u);
x_71 = lean_nat_div(x_69, x_70);
lean_dec(x_69);
x_72 = lean_array_get_size(x_67);
x_73 = lean_nat_dec_le(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_67);
lean_ctor_set(x_43, 1, x_74);
lean_ctor_set(x_43, 0, x_65);
x_75 = lean_st_ref_set(x_8, x_42, x_44);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_6);
x_18 = x_77;
x_19 = x_76;
goto block_26;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_ctor_set(x_43, 1, x_67);
lean_ctor_set(x_43, 0, x_65);
x_78 = lean_st_ref_set(x_8, x_42, x_44);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_6);
x_18 = x_80;
x_19 = x_79;
goto block_26;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_box(0);
x_82 = lean_array_uset(x_49, x_62, x_81);
x_83 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_39, x_40, x_63);
x_84 = lean_array_uset(x_82, x_62, x_83);
lean_ctor_set(x_43, 1, x_84);
x_85 = lean_st_ref_set(x_8, x_42, x_44);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_6);
x_18 = x_87;
x_19 = x_86;
goto block_26;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint64_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; size_t x_98; size_t x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
x_88 = lean_ctor_get(x_43, 0);
x_89 = lean_ctor_get(x_43, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = lean_array_get_size(x_89);
x_91 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_39);
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
x_103 = lean_array_uget(x_89, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_39, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_105 = lean_nat_add(x_88, x_37);
lean_dec(x_88);
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_40);
lean_ctor_set(x_106, 2, x_103);
x_107 = lean_array_uset(x_89, x_102, x_106);
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
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_107);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_105);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_42, 0, x_115);
x_116 = lean_st_ref_set(x_8, x_42, x_44);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_6);
x_18 = x_118;
x_19 = x_117;
goto block_26;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_105);
lean_ctor_set(x_119, 1, x_107);
lean_ctor_set(x_42, 0, x_119);
x_120 = lean_st_ref_set(x_8, x_42, x_44);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_6);
x_18 = x_122;
x_19 = x_121;
goto block_26;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_123 = lean_box(0);
x_124 = lean_array_uset(x_89, x_102, x_123);
x_125 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_39, x_40, x_103);
x_126 = lean_array_uset(x_124, x_102, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_88);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_42, 0, x_127);
x_128 = lean_st_ref_set(x_8, x_42, x_44);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_6);
x_18 = x_130;
x_19 = x_129;
goto block_26;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; size_t x_149; size_t x_150; size_t x_151; size_t x_152; size_t x_153; lean_object* x_154; uint8_t x_155; 
x_131 = lean_ctor_get(x_42, 1);
x_132 = lean_ctor_get(x_42, 2);
x_133 = lean_ctor_get(x_42, 3);
x_134 = lean_ctor_get_uint8(x_42, sizeof(void*)*7);
x_135 = lean_ctor_get(x_42, 4);
x_136 = lean_ctor_get(x_42, 5);
x_137 = lean_ctor_get(x_42, 6);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_42);
x_138 = lean_ctor_get(x_43, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_43, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_140 = x_43;
} else {
 lean_dec_ref(x_43);
 x_140 = lean_box(0);
}
x_141 = lean_array_get_size(x_139);
x_142 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_39);
x_143 = 32;
x_144 = lean_uint64_shift_right(x_142, x_143);
x_145 = lean_uint64_xor(x_142, x_144);
x_146 = 16;
x_147 = lean_uint64_shift_right(x_145, x_146);
x_148 = lean_uint64_xor(x_145, x_147);
x_149 = lean_uint64_to_usize(x_148);
x_150 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_151 = 1;
x_152 = lean_usize_sub(x_150, x_151);
x_153 = lean_usize_land(x_149, x_152);
x_154 = lean_array_uget(x_139, x_153);
x_155 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_39, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_nat_add(x_138, x_37);
lean_dec(x_138);
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_39);
lean_ctor_set(x_157, 1, x_40);
lean_ctor_set(x_157, 2, x_154);
x_158 = lean_array_uset(x_139, x_153, x_157);
x_159 = lean_unsigned_to_nat(4u);
x_160 = lean_nat_mul(x_156, x_159);
x_161 = lean_unsigned_to_nat(3u);
x_162 = lean_nat_div(x_160, x_161);
lean_dec(x_160);
x_163 = lean_array_get_size(x_158);
x_164 = lean_nat_dec_le(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_158);
if (lean_is_scalar(x_140)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_140;
}
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_131);
lean_ctor_set(x_167, 2, x_132);
lean_ctor_set(x_167, 3, x_133);
lean_ctor_set(x_167, 4, x_135);
lean_ctor_set(x_167, 5, x_136);
lean_ctor_set(x_167, 6, x_137);
lean_ctor_set_uint8(x_167, sizeof(void*)*7, x_134);
x_168 = lean_st_ref_set(x_8, x_167, x_44);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_6);
x_18 = x_170;
x_19 = x_169;
goto block_26;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
if (lean_is_scalar(x_140)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_140;
}
lean_ctor_set(x_171, 0, x_156);
lean_ctor_set(x_171, 1, x_158);
x_172 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_131);
lean_ctor_set(x_172, 2, x_132);
lean_ctor_set(x_172, 3, x_133);
lean_ctor_set(x_172, 4, x_135);
lean_ctor_set(x_172, 5, x_136);
lean_ctor_set(x_172, 6, x_137);
lean_ctor_set_uint8(x_172, sizeof(void*)*7, x_134);
x_173 = lean_st_ref_set(x_8, x_172, x_44);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_6);
x_18 = x_175;
x_19 = x_174;
goto block_26;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_176 = lean_box(0);
x_177 = lean_array_uset(x_139, x_153, x_176);
x_178 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_39, x_40, x_154);
x_179 = lean_array_uset(x_177, x_153, x_178);
if (lean_is_scalar(x_140)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_140;
}
lean_ctor_set(x_180, 0, x_138);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_131);
lean_ctor_set(x_181, 2, x_132);
lean_ctor_set(x_181, 3, x_133);
lean_ctor_set(x_181, 4, x_135);
lean_ctor_set(x_181, 5, x_136);
lean_ctor_set(x_181, 6, x_137);
lean_ctor_set_uint8(x_181, sizeof(void*)*7, x_134);
x_182 = lean_st_ref_set(x_8, x_181, x_44);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_6);
x_18 = x_184;
x_19 = x_183;
goto block_26;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; size_t x_214; size_t x_215; size_t x_216; size_t x_217; size_t x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_6);
x_185 = lean_array_fget(x_27, x_28);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_28, x_186);
lean_dec(x_28);
x_188 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_188, 0, x_27);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_188, 2, x_29);
x_189 = lean_ctor_get(x_17, 0);
lean_inc(x_189);
lean_dec(x_17);
x_190 = l_Lean_Compiler_LCNF_Arg_toExpr(x_185);
x_191 = lean_st_ref_take(x_8, x_14);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 3);
lean_inc(x_197);
x_198 = lean_ctor_get_uint8(x_192, sizeof(void*)*7);
x_199 = lean_ctor_get(x_192, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_192, 5);
lean_inc(x_200);
x_201 = lean_ctor_get(x_192, 6);
lean_inc(x_201);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 lean_ctor_release(x_192, 6);
 x_202 = x_192;
} else {
 lean_dec_ref(x_192);
 x_202 = lean_box(0);
}
x_203 = lean_ctor_get(x_193, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_205 = x_193;
} else {
 lean_dec_ref(x_193);
 x_205 = lean_box(0);
}
x_206 = lean_array_get_size(x_204);
x_207 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_189);
x_208 = 32;
x_209 = lean_uint64_shift_right(x_207, x_208);
x_210 = lean_uint64_xor(x_207, x_209);
x_211 = 16;
x_212 = lean_uint64_shift_right(x_210, x_211);
x_213 = lean_uint64_xor(x_210, x_212);
x_214 = lean_uint64_to_usize(x_213);
x_215 = lean_usize_of_nat(x_206);
lean_dec(x_206);
x_216 = 1;
x_217 = lean_usize_sub(x_215, x_216);
x_218 = lean_usize_land(x_214, x_217);
x_219 = lean_array_uget(x_204, x_218);
x_220 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_Compiler_LCNF_addFVarSubst___spec__1(x_189, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_221 = lean_nat_add(x_203, x_186);
lean_dec(x_203);
x_222 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_222, 0, x_189);
lean_ctor_set(x_222, 1, x_190);
lean_ctor_set(x_222, 2, x_219);
x_223 = lean_array_uset(x_204, x_218, x_222);
x_224 = lean_unsigned_to_nat(4u);
x_225 = lean_nat_mul(x_221, x_224);
x_226 = lean_unsigned_to_nat(3u);
x_227 = lean_nat_div(x_225, x_226);
lean_dec(x_225);
x_228 = lean_array_get_size(x_223);
x_229 = lean_nat_dec_le(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_Compiler_LCNF_addFVarSubst___spec__2(x_223);
if (lean_is_scalar(x_205)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_205;
}
lean_ctor_set(x_231, 0, x_221);
lean_ctor_set(x_231, 1, x_230);
if (lean_is_scalar(x_202)) {
 x_232 = lean_alloc_ctor(0, 7, 1);
} else {
 x_232 = x_202;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_195);
lean_ctor_set(x_232, 2, x_196);
lean_ctor_set(x_232, 3, x_197);
lean_ctor_set(x_232, 4, x_199);
lean_ctor_set(x_232, 5, x_200);
lean_ctor_set(x_232, 6, x_201);
lean_ctor_set_uint8(x_232, sizeof(void*)*7, x_198);
x_233 = lean_st_ref_set(x_8, x_232, x_194);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_188);
x_18 = x_235;
x_19 = x_234;
goto block_26;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
if (lean_is_scalar(x_205)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_205;
}
lean_ctor_set(x_236, 0, x_221);
lean_ctor_set(x_236, 1, x_223);
if (lean_is_scalar(x_202)) {
 x_237 = lean_alloc_ctor(0, 7, 1);
} else {
 x_237 = x_202;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_195);
lean_ctor_set(x_237, 2, x_196);
lean_ctor_set(x_237, 3, x_197);
lean_ctor_set(x_237, 4, x_199);
lean_ctor_set(x_237, 5, x_200);
lean_ctor_set(x_237, 6, x_201);
lean_ctor_set_uint8(x_237, sizeof(void*)*7, x_198);
x_238 = lean_st_ref_set(x_8, x_237, x_194);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_188);
x_18 = x_240;
x_19 = x_239;
goto block_26;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_241 = lean_box(0);
x_242 = lean_array_uset(x_204, x_218, x_241);
x_243 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_Compiler_LCNF_addFVarSubst___spec__5(x_189, x_190, x_219);
x_244 = lean_array_uset(x_242, x_218, x_243);
if (lean_is_scalar(x_205)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_205;
}
lean_ctor_set(x_245, 0, x_203);
lean_ctor_set(x_245, 1, x_244);
if (lean_is_scalar(x_202)) {
 x_246 = lean_alloc_ctor(0, 7, 1);
} else {
 x_246 = x_202;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_195);
lean_ctor_set(x_246, 2, x_196);
lean_ctor_set(x_246, 3, x_197);
lean_ctor_set(x_246, 4, x_199);
lean_ctor_set(x_246, 5, x_200);
lean_ctor_set(x_246, 6, x_201);
lean_ctor_set_uint8(x_246, sizeof(void*)*7, x_198);
x_247 = lean_st_ref_set(x_8, x_246, x_194);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_188);
x_18 = x_249;
x_19 = x_248;
goto block_26;
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
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
x_45 = lean_box(0);
x_46 = lean_array_size(x_38);
x_47 = 0;
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_38, x_45, x_38, x_46, x_47, x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
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
x_305 = lean_box(0);
x_306 = lean_array_size(x_298);
x_307 = 0;
x_308 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_298, x_305, x_298, x_306, x_307, x_304, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_297);
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
x_437 = lean_box(0);
x_438 = lean_array_size(x_430);
x_439 = 0;
x_440 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_430, x_437, x_430, x_438, x_439, x_436, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_429);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Simp_simp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_2);
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
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_6);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
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
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__5);
l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6 = _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__6);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
