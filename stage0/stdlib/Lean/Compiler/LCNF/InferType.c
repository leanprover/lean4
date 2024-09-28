// Lean compiler output
// Module: Lean.Compiler.LCNF.InferType
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.OtherDecl
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6;
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3;
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType(lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__1;
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___boxed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getLevel___closed__1;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3;
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_AltCore_getCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3;
static lean_object* l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getLevel___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLetValueType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2;
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getBinderName(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_userName(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_getBinderName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getType(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_type(x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_getType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_instInhabitedExpr;
x_17 = l_outOfBounds___rarg(x_16);
x_18 = l_Lean_Expr_fvarId_x21(x_17);
lean_dec(x_17);
lean_inc(x_4);
lean_inc(x_18);
x_19 = l_Lean_Compiler_LCNF_InferType_getBinderName(x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_4);
x_22 = l_Lean_Compiler_LCNF_InferType_getType(x_18, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_expr_abstract_range(x_23, x_13, x_1);
lean_dec(x_23);
x_26 = 0;
x_27 = l_Lean_Expr_forallE___override(x_20, x_25, x_3, x_26);
x_2 = x_13;
x_3 = x_27;
x_9 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_array_fget(x_1, x_13);
x_38 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
lean_inc(x_4);
lean_inc(x_38);
x_39 = l_Lean_Compiler_LCNF_InferType_getBinderName(x_38, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_4);
x_42 = l_Lean_Compiler_LCNF_InferType_getType(x_38, x_4, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_expr_abstract_range(x_43, x_13, x_1);
lean_dec(x_43);
x_46 = 0;
x_47 = l_Lean_Expr_forallE___override(x_40, x_45, x_3, x_46);
x_2 = x_13;
x_3 = x_47;
x_9 = x_44;
goto _start;
}
else
{
uint8_t x_49; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_57; 
lean_dec(x_4);
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_9);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_abstract(x_2, x_1);
x_10 = lean_array_get_size(x_1);
x_11 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(x_1, x_10, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldRevM_loop___at_Lean_Compiler_LCNF_InferType_mkForallFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4;
x_3 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_9, x_10, x_1);
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_13 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_mkForallParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_num___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
x_27 = lean_ctor_get(x_14, 5);
x_28 = lean_ctor_get(x_14, 6);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_5);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_27);
lean_ctor_set(x_29, 6, x_28);
x_30 = lean_st_ref_set(x_1, x_29, x_15);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
lean_inc(x_35);
lean_inc(x_34);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_35, x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_st_ref_take(x_1, x_6);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_41, 6);
lean_inc(x_48);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 lean_ctor_release(x_41, 4);
 lean_ctor_release(x_41, 5);
 lean_ctor_release(x_41, 6);
 x_49 = x_41;
} else {
 lean_dec_ref(x_41);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 7, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_44);
lean_ctor_set(x_50, 2, x_39);
lean_ctor_set(x_50, 3, x_45);
lean_ctor_set(x_50, 4, x_46);
lean_ctor_set(x_50, 5, x_47);
lean_ctor_set(x_50, 6, x_48);
x_51 = lean_st_ref_set(x_1, x_50, x_42);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Expr_fvar___override(x_12);
x_15 = 0;
x_16 = l_Lean_LocalContext_mkLocalDecl(x_5, x_12, x_1, x_2, x_3, x_15);
x_17 = lean_apply_7(x_4, x_14, x_16, x_6, x_7, x_8, x_9, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkFreshId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2;
x_9 = lean_name_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_getDecl_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Compiler_LCNF_getOtherDeclType(x_1, x_2, x_3, x_4, x_5, x_6, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_16, x_2);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_19, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Compiler_LCNF_erasedExpr;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_14 = lean_expr_instantiate_rev(x_11, x_3);
lean_dec(x_11);
x_15 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l_Lean_Expr_fvar___override(x_16);
x_19 = 0;
x_20 = l_Lean_LocalContext_mkLocalDecl(x_4, x_16, x_10, x_14, x_13, x_19);
lean_inc(x_18);
x_21 = lean_array_push(x_2, x_18);
x_22 = lean_array_push(x_3, x_18);
x_1 = x_12;
x_2 = x_21;
x_3 = x_22;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
case 8:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_expr_instantiate_rev(x_25, x_3);
lean_dec(x_25);
x_28 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_4, x_5, x_6, x_7, x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = l_Lean_Expr_fvar___override(x_29);
x_32 = 0;
x_33 = 0;
x_34 = l_Lean_LocalContext_mkLocalDecl(x_4, x_29, x_24, x_27, x_32, x_33);
x_35 = lean_array_push(x_3, x_31);
x_1 = x_26;
x_3 = x_35;
x_4 = x_34;
x_9 = x_30;
goto _start;
}
default: 
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Compiler_LCNF_InferType_inferType(x_37, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_39);
lean_dec(x_2);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4;
x_9 = lean_panic_fn(x_8, x_1);
x_10 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.InferType", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.InferType.inferType", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
x_2 = l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
x_3 = lean_unsigned_to_nat(124u);
x_4 = lean_unsigned_to_nat(73u);
x_5 = l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_InferType_getType(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Level_succ___override(x_10);
x_12 = l_Lean_Expr_sort___override(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
case 4:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_InferType_inferConstType(x_14, x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
case 5:
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
case 6:
{
lean_object* x_18; 
x_18 = l_Lean_Compiler_LCNF_InferType_inferLambdaType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
case 7:
{
lean_object* x_19; 
x_19 = l_Lean_Compiler_LCNF_InferType_inferForallType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = l_Lean_Compiler_LCNF_InferType_inferType___closed__4;
x_21 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
x_9 = l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(x_1, x_8, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1;
x_9 = l_Lean_Compiler_LCNF_InferType_inferForallType_go(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_erasedExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_uget(x_2, x_4);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_19, x_6, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_21, 0, x_5);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = l_Lean_mkLevelIMax_x27(x_30, x_16);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_31);
lean_ctor_set(x_5, 0, x_1);
x_32 = 1;
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_11 = x_29;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_18);
if (x_39 == 0)
{
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_45, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = l_Lean_mkLevelIMax_x27(x_55, x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_4, x_58);
x_4 = x_59;
x_5 = x_57;
x_11 = x_54;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_63 = x_47;
} else {
 lean_dec_ref(x_47);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_65 = lean_ctor_get(x_44, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_67 = x_44;
} else {
 lean_dec_ref(x_44);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Level_normalize(x_1);
x_10 = l_Lean_Expr_sort___override(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_9, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
x_14 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Compiler_LCNF_erasedExpr;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l_Array_reverse___rarg(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_array_size(x_20);
x_24 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(x_21, x_20, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_29, x_30, x_3, x_4, x_5, x_6, x_7, x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
case 1:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_47 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_46, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lean_Compiler_LCNF_erasedExpr;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = l_Array_reverse___rarg(x_2);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
x_60 = lean_array_size(x_57);
x_61 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(x_58, x_57, x_60, x_61, x_59, x_3, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_box(0);
x_68 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_66, x_67, x_3, x_4, x_5, x_6, x_7, x_65);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_66);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_63);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_62);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_62, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_71);
return x_62;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_dec(x_62);
x_73 = lean_ctor_get(x_64, 0);
lean_inc(x_73);
lean_dec(x_64);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_62);
if (x_75 == 0)
{
return x_62;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_62);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_47);
if (x_79 == 0)
{
return x_47;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_47, 0);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_47);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 2:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_84 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_83, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = l_Lean_Compiler_LCNF_erasedExpr;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
lean_dec(x_85);
x_94 = l_Array_reverse___rarg(x_2);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_97 = lean_array_size(x_94);
x_98 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_99 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(x_95, x_94, x_97, x_98, x_96, x_3, x_4, x_5, x_6, x_7, x_92);
lean_dec(x_94);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_box(0);
x_105 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_103, x_104, x_3, x_4, x_5, x_6, x_7, x_102);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_103);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_100);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_99);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_99, 0);
lean_dec(x_107);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
lean_ctor_set(x_99, 0, x_108);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_99, 1);
lean_inc(x_109);
lean_dec(x_99);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
lean_dec(x_101);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = !lean_is_exclusive(x_99);
if (x_112 == 0)
{
return x_99;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_99, 0);
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_99);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_84);
if (x_116 == 0)
{
return x_84;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_84, 0);
x_118 = lean_ctor_get(x_84, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_84);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
case 3:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_121 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_120, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 0);
lean_dec(x_124);
x_125 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_121, 0, x_125);
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = l_Lean_Compiler_LCNF_erasedExpr;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; lean_object* x_136; 
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
lean_dec(x_121);
x_130 = lean_ctor_get(x_122, 0);
lean_inc(x_130);
lean_dec(x_122);
x_131 = l_Array_reverse___rarg(x_2);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
x_134 = lean_array_size(x_131);
x_135 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_136 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(x_132, x_131, x_134, x_135, x_133, x_3, x_4, x_5, x_6, x_7, x_129);
lean_dec(x_131);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_box(0);
x_142 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_140, x_141, x_3, x_4, x_5, x_6, x_7, x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_140);
return x_142;
}
else
{
uint8_t x_143; 
lean_dec(x_137);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_136);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_136, 0);
lean_dec(x_144);
x_145 = lean_ctor_get(x_138, 0);
lean_inc(x_145);
lean_dec(x_138);
lean_ctor_set(x_136, 0, x_145);
return x_136;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_136, 1);
lean_inc(x_146);
lean_dec(x_136);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
lean_dec(x_138);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_136);
if (x_149 == 0)
{
return x_136;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_136, 0);
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_136);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_121);
if (x_153 == 0)
{
return x_121;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_121, 0);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_121);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
case 4:
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_158 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_157, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_158, 0);
lean_dec(x_161);
x_162 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_158, 0, x_162);
return x_158;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_158, 1);
lean_inc(x_163);
lean_dec(x_158);
x_164 = l_Lean_Compiler_LCNF_erasedExpr;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; lean_object* x_173; 
x_166 = lean_ctor_get(x_158, 1);
lean_inc(x_166);
lean_dec(x_158);
x_167 = lean_ctor_get(x_159, 0);
lean_inc(x_167);
lean_dec(x_159);
x_168 = l_Array_reverse___rarg(x_2);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
x_171 = lean_array_size(x_168);
x_172 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_173 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(x_169, x_168, x_171, x_172, x_170, x_3, x_4, x_5, x_6, x_7, x_166);
lean_dec(x_168);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_box(0);
x_179 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_177, x_178, x_3, x_4, x_5, x_6, x_7, x_176);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_177);
return x_179;
}
else
{
uint8_t x_180; 
lean_dec(x_174);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_180 = !lean_is_exclusive(x_173);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_173, 0);
lean_dec(x_181);
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
lean_dec(x_175);
lean_ctor_set(x_173, 0, x_182);
return x_173;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_dec(x_173);
x_184 = lean_ctor_get(x_175, 0);
lean_inc(x_184);
lean_dec(x_175);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_186 = !lean_is_exclusive(x_173);
if (x_186 == 0)
{
return x_173;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_173, 0);
x_188 = lean_ctor_get(x_173, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_173);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_190 = !lean_is_exclusive(x_158);
if (x_190 == 0)
{
return x_158;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_158, 0);
x_192 = lean_ctor_get(x_158, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_158);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
case 5:
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_195 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_194, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = !lean_is_exclusive(x_195);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_195, 0);
lean_dec(x_198);
x_199 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_195, 0, x_199);
return x_195;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_195, 1);
lean_inc(x_200);
lean_dec(x_195);
x_201 = l_Lean_Compiler_LCNF_erasedExpr;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; 
x_203 = lean_ctor_get(x_195, 1);
lean_inc(x_203);
lean_dec(x_195);
x_204 = lean_ctor_get(x_196, 0);
lean_inc(x_204);
lean_dec(x_196);
x_205 = l_Array_reverse___rarg(x_2);
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
x_208 = lean_array_size(x_205);
x_209 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_210 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(x_206, x_205, x_208, x_209, x_207, x_3, x_4, x_5, x_6, x_7, x_203);
lean_dec(x_205);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_215 = lean_box(0);
x_216 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_214, x_215, x_3, x_4, x_5, x_6, x_7, x_213);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_214);
return x_216;
}
else
{
uint8_t x_217; 
lean_dec(x_211);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_217 = !lean_is_exclusive(x_210);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_210, 0);
lean_dec(x_218);
x_219 = lean_ctor_get(x_212, 0);
lean_inc(x_219);
lean_dec(x_212);
lean_ctor_set(x_210, 0, x_219);
return x_210;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_210, 1);
lean_inc(x_220);
lean_dec(x_210);
x_221 = lean_ctor_get(x_212, 0);
lean_inc(x_221);
lean_dec(x_212);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
else
{
uint8_t x_223; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_210);
if (x_223 == 0)
{
return x_210;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_210, 0);
x_225 = lean_ctor_get(x_210, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_210);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_227 = !lean_is_exclusive(x_195);
if (x_227 == 0)
{
return x_195;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_195, 0);
x_229 = lean_ctor_get(x_195, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_195);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
case 6:
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_232 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_231, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_234 = !lean_is_exclusive(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_232, 0);
lean_dec(x_235);
x_236 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_232, 0, x_236);
return x_232;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_232, 1);
lean_inc(x_237);
lean_dec(x_232);
x_238 = l_Lean_Compiler_LCNF_erasedExpr;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_237);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; size_t x_245; size_t x_246; lean_object* x_247; 
x_240 = lean_ctor_get(x_232, 1);
lean_inc(x_240);
lean_dec(x_232);
x_241 = lean_ctor_get(x_233, 0);
lean_inc(x_241);
lean_dec(x_233);
x_242 = l_Array_reverse___rarg(x_2);
x_243 = lean_box(0);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
x_245 = lean_array_size(x_242);
x_246 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_247 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(x_243, x_242, x_245, x_246, x_244, x_3, x_4, x_5, x_6, x_7, x_240);
lean_dec(x_242);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = lean_box(0);
x_253 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_251, x_252, x_3, x_4, x_5, x_6, x_7, x_250);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_251);
return x_253;
}
else
{
uint8_t x_254; 
lean_dec(x_248);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_254 = !lean_is_exclusive(x_247);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_247, 0);
lean_dec(x_255);
x_256 = lean_ctor_get(x_249, 0);
lean_inc(x_256);
lean_dec(x_249);
lean_ctor_set(x_247, 0, x_256);
return x_247;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_247, 1);
lean_inc(x_257);
lean_dec(x_247);
x_258 = lean_ctor_get(x_249, 0);
lean_inc(x_258);
lean_dec(x_249);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_260 = !lean_is_exclusive(x_247);
if (x_260 == 0)
{
return x_247;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_247, 0);
x_262 = lean_ctor_get(x_247, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_247);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_264 = !lean_is_exclusive(x_232);
if (x_264 == 0)
{
return x_232;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_232, 0);
x_266 = lean_ctor_get(x_232, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_232);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
case 7:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; 
x_268 = lean_ctor_get(x_1, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_1, 1);
lean_inc(x_269);
x_270 = lean_ctor_get(x_1, 2);
lean_inc(x_270);
x_271 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_272 = lean_expr_instantiate_rev(x_269, x_2);
lean_dec(x_269);
x_273 = l_Lean_mkFreshFVarId___at_Lean_Compiler_LCNF_InferType_withLocalDecl___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
lean_inc(x_274);
x_276 = l_Lean_Expr_fvar___override(x_274);
x_277 = 0;
x_278 = l_Lean_LocalContext_mkLocalDecl(x_3, x_274, x_268, x_272, x_271, x_277);
x_279 = lean_array_push(x_2, x_276);
x_1 = x_270;
x_2 = x_279;
x_3 = x_278;
x_8 = x_275;
goto _start;
}
case 8:
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_282 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_281, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_obj_tag(x_283) == 0)
{
uint8_t x_284; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_284 = !lean_is_exclusive(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_282, 0);
lean_dec(x_285);
x_286 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_282, 0, x_286);
return x_282;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
lean_dec(x_282);
x_288 = l_Lean_Compiler_LCNF_erasedExpr;
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; size_t x_295; size_t x_296; lean_object* x_297; 
x_290 = lean_ctor_get(x_282, 1);
lean_inc(x_290);
lean_dec(x_282);
x_291 = lean_ctor_get(x_283, 0);
lean_inc(x_291);
lean_dec(x_283);
x_292 = l_Array_reverse___rarg(x_2);
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
x_295 = lean_array_size(x_292);
x_296 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_297 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(x_293, x_292, x_295, x_296, x_294, x_3, x_4, x_5, x_6, x_7, x_290);
lean_dec(x_292);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_box(0);
x_303 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_301, x_302, x_3, x_4, x_5, x_6, x_7, x_300);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_301);
return x_303;
}
else
{
uint8_t x_304; 
lean_dec(x_298);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_304 = !lean_is_exclusive(x_297);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_297, 0);
lean_dec(x_305);
x_306 = lean_ctor_get(x_299, 0);
lean_inc(x_306);
lean_dec(x_299);
lean_ctor_set(x_297, 0, x_306);
return x_297;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_297, 1);
lean_inc(x_307);
lean_dec(x_297);
x_308 = lean_ctor_get(x_299, 0);
lean_inc(x_308);
lean_dec(x_299);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_310 = !lean_is_exclusive(x_297);
if (x_310 == 0)
{
return x_297;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_297, 0);
x_312 = lean_ctor_get(x_297, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_297);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_314 = !lean_is_exclusive(x_282);
if (x_314 == 0)
{
return x_282;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_282, 0);
x_316 = lean_ctor_get(x_282, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_282);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
case 9:
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_319 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_318, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_321 = !lean_is_exclusive(x_319);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_319, 0);
lean_dec(x_322);
x_323 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_319, 0, x_323);
return x_319;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
lean_dec(x_319);
x_325 = l_Lean_Compiler_LCNF_erasedExpr;
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
return x_326;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; size_t x_332; size_t x_333; lean_object* x_334; 
x_327 = lean_ctor_get(x_319, 1);
lean_inc(x_327);
lean_dec(x_319);
x_328 = lean_ctor_get(x_320, 0);
lean_inc(x_328);
lean_dec(x_320);
x_329 = l_Array_reverse___rarg(x_2);
x_330 = lean_box(0);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_328);
x_332 = lean_array_size(x_329);
x_333 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_334 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(x_330, x_329, x_332, x_333, x_331, x_3, x_4, x_5, x_6, x_7, x_327);
lean_dec(x_329);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_339 = lean_box(0);
x_340 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_338, x_339, x_3, x_4, x_5, x_6, x_7, x_337);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_338);
return x_340;
}
else
{
uint8_t x_341; 
lean_dec(x_335);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_341 = !lean_is_exclusive(x_334);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_334, 0);
lean_dec(x_342);
x_343 = lean_ctor_get(x_336, 0);
lean_inc(x_343);
lean_dec(x_336);
lean_ctor_set(x_334, 0, x_343);
return x_334;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_334, 1);
lean_inc(x_344);
lean_dec(x_334);
x_345 = lean_ctor_get(x_336, 0);
lean_inc(x_345);
lean_dec(x_336);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_344);
return x_346;
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_347 = !lean_is_exclusive(x_334);
if (x_347 == 0)
{
return x_334;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_334, 0);
x_349 = lean_ctor_get(x_334, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_334);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_351 = !lean_is_exclusive(x_319);
if (x_351 == 0)
{
return x_319;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_319, 0);
x_353 = lean_ctor_get(x_319, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_319);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
case 10:
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_356 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_355, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
uint8_t x_358; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_358 = !lean_is_exclusive(x_356);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_356, 0);
lean_dec(x_359);
x_360 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_356, 0, x_360);
return x_356;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_356, 1);
lean_inc(x_361);
lean_dec(x_356);
x_362 = l_Lean_Compiler_LCNF_erasedExpr;
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; size_t x_369; size_t x_370; lean_object* x_371; 
x_364 = lean_ctor_get(x_356, 1);
lean_inc(x_364);
lean_dec(x_356);
x_365 = lean_ctor_get(x_357, 0);
lean_inc(x_365);
lean_dec(x_357);
x_366 = l_Array_reverse___rarg(x_2);
x_367 = lean_box(0);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_365);
x_369 = lean_array_size(x_366);
x_370 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_371 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(x_367, x_366, x_369, x_370, x_368, x_3, x_4, x_5, x_6, x_7, x_364);
lean_dec(x_366);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_371, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_ctor_get(x_371, 1);
lean_inc(x_374);
lean_dec(x_371);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_dec(x_372);
x_376 = lean_box(0);
x_377 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_375, x_376, x_3, x_4, x_5, x_6, x_7, x_374);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_375);
return x_377;
}
else
{
uint8_t x_378; 
lean_dec(x_372);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_378 = !lean_is_exclusive(x_371);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_371, 0);
lean_dec(x_379);
x_380 = lean_ctor_get(x_373, 0);
lean_inc(x_380);
lean_dec(x_373);
lean_ctor_set(x_371, 0, x_380);
return x_371;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_371, 1);
lean_inc(x_381);
lean_dec(x_371);
x_382 = lean_ctor_get(x_373, 0);
lean_inc(x_382);
lean_dec(x_373);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_384 = !lean_is_exclusive(x_371);
if (x_384 == 0)
{
return x_371;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_371, 0);
x_386 = lean_ctor_get(x_371, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_371);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = !lean_is_exclusive(x_356);
if (x_388 == 0)
{
return x_356;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_356, 0);
x_390 = lean_ctor_get(x_356, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_356);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
default: 
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_393 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_392, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_obj_tag(x_394) == 0)
{
uint8_t x_395; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_395 = !lean_is_exclusive(x_393);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_393, 0);
lean_dec(x_396);
x_397 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_393, 0, x_397);
return x_393;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_393, 1);
lean_inc(x_398);
lean_dec(x_393);
x_399 = l_Lean_Compiler_LCNF_erasedExpr;
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; size_t x_406; size_t x_407; lean_object* x_408; 
x_401 = lean_ctor_get(x_393, 1);
lean_inc(x_401);
lean_dec(x_393);
x_402 = lean_ctor_get(x_394, 0);
lean_inc(x_402);
lean_dec(x_394);
x_403 = l_Array_reverse___rarg(x_2);
x_404 = lean_box(0);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_402);
x_406 = lean_array_size(x_403);
x_407 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_408 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(x_404, x_403, x_406, x_407, x_405, x_3, x_4, x_5, x_6, x_7, x_401);
lean_dec(x_403);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_dec(x_408);
x_412 = lean_ctor_get(x_409, 1);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_box(0);
x_414 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_412, x_413, x_3, x_4, x_5, x_6, x_7, x_411);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_412);
return x_414;
}
else
{
uint8_t x_415; 
lean_dec(x_409);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_415 = !lean_is_exclusive(x_408);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_408, 0);
lean_dec(x_416);
x_417 = lean_ctor_get(x_410, 0);
lean_inc(x_417);
lean_dec(x_410);
lean_ctor_set(x_408, 0, x_417);
return x_408;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_408, 1);
lean_inc(x_418);
lean_dec(x_408);
x_419 = lean_ctor_get(x_410, 0);
lean_inc(x_419);
lean_dec(x_410);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
}
else
{
uint8_t x_421; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_421 = !lean_is_exclusive(x_408);
if (x_421 == 0)
{
return x_408;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_408, 0);
x_423 = lean_ctor_get(x_408, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_408);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
}
else
{
uint8_t x_425; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_425 = !lean_is_exclusive(x_393);
if (x_425 == 0)
{
return x_393;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_393, 0);
x_427 = lean_ctor_get(x_393, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_393);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 3)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_headBeta(x_28);
if (lean_obj_tag(x_30) == 7)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_19 = x_34;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_expr_instantiate_rev_range(x_30, x_29, x_4, x_1);
lean_dec(x_30);
x_36 = l_Lean_Expr_headBeta(x_35);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_19 = x_40;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_29);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_19 = x_44;
x_20 = x_13;
goto block_26;
}
}
block_26:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_24;
x_7 = x_23;
x_13 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_13);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_7);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_expr_instantiate_rev_range(x_1, x_2, x_3, x_4);
x_13 = l_Lean_Expr_headBeta(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_InferType_inferType(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_12);
x_14 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_19);
x_23 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1(x_18, x_20, x_19, x_12, x_19, x_16, x_22, x_2, x_3, x_4, x_5, x_6, x_11);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1(x_28, x_29, x_19, x_18, x_30, x_2, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_18);
lean_dec(x_19);
lean_dec(x_29);
lean_dec(x_28);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_23);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_23, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
return x_9;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__3(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__4(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__5(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__6(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__7(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__8(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__9(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__10(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__11(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_inferForallType_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_InferType_inferAppType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_Compiler_LCNF_erasedExpr;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_getType(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Compiler_LCNF_InferType_inferType(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_headBeta(x_28);
if (lean_obj_tag(x_30) == 7)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_inc(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_19 = x_34;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_30, x_29, x_4, x_1);
lean_dec(x_30);
x_36 = l_Lean_Expr_headBeta(x_35);
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
lean_inc(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_2);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_19 = x_40;
x_20 = x_13;
goto block_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_29);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_19 = x_44;
x_20 = x_13;
goto block_26;
}
}
block_26:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_18;
x_4 = x_24;
x_7 = x_23;
x_13 = x_20;
goto _start;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_13);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_7);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_1, x_2, x_3, x_4);
x_13 = l_Lean_Expr_headBeta(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
lean_inc(x_2);
x_15 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(x_2, x_10, x_9, x_11, x_9, x_14, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(x_20, x_21, x_9, x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_9);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferAppTypeCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_4, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_21);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_9);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_29);
lean_inc(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_4, x_33);
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
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_5, 2);
x_42 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_1);
lean_inc(x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_38;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_4, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_21);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_9);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_29);
lean_inc(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_4, x_33);
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
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_5, 2);
x_42 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_1);
lean_inc(x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_38;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(x_20, x_2, x_3, x_4, x_5, x_6, x_11);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = lean_environment_find(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_box(0);
x_28 = l_Lean_Expr_const___override(x_1, x_27);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(x_33, x_2, x_3, x_4, x_5, x_6, x_24);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_24);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_4, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_21);
lean_inc(x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_9);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_5, 2);
x_28 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 0, x_29);
lean_inc(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_4, x_33);
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
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_5, 2);
x_42 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_1);
lean_inc(x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_8);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_38)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_38;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid projection", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_Expr_proj___override(x_2, x_3, x_13);
x_15 = l_Lean_indentExpr(x_14);
x_16 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(x_19, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_38; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_5, x_19);
lean_dec(x_5);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
if (lean_obj_tag(x_38) == 7)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_hasLooseBVars(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_4);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_15);
x_21 = x_43;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = l_Lean_Compiler_LCNF_erasedExpr;
x_45 = lean_expr_instantiate1(x_39, x_44);
lean_dec(x_39);
lean_inc(x_4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
x_21 = x_48;
goto block_37;
}
}
else
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isErased(x_38);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_51 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1(x_3, x_1, x_2, x_4, x_38, x_50, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_38);
x_21 = x_51;
goto block_37;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_15);
x_21 = x_55;
goto block_37;
}
}
block_37:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_20;
x_6 = x_31;
x_9 = x_30;
x_15 = x_29;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_56; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_9);
lean_ctor_set(x_56, 1, x_15);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_9);
lean_ctor_set(x_57, 1, x_15);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Expr_fvar___override(x_1);
x_12 = l_Lean_Expr_proj___override(x_2, x_3, x_11);
x_13 = l_Lean_indentExpr(x_12);
x_14 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_17, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isErased(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_Compiler_LCNF_erasedExpr;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Compiler_LCNF_InferType_getType(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_headBeta(x_12);
x_15 = l_Lean_Expr_isErased(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_10);
x_16 = l_Lean_Expr_getAppFn(x_14);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_find(x_23, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
lean_dec(x_14);
x_25 = l_Lean_Expr_fvar___override(x_3);
x_26 = l_Lean_Expr_proj___override(x_1, x_2, x_25);
x_27 = l_Lean_indentExpr(x_26);
x_28 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_28);
x_29 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_30, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
if (lean_obj_tag(x_32) == 5)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get_uint8(x_33, sizeof(void*)*6);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_14);
x_38 = l_Lean_Expr_fvar___override(x_3);
x_39 = l_Lean_Expr_proj___override(x_1, x_2, x_38);
x_40 = l_Lean_indentExpr(x_39);
x_41 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_41);
x_42 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_19);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_43, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_44;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_33, 4);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_14);
x_46 = l_Lean_Expr_fvar___override(x_3);
x_47 = l_Lean_Expr_proj___override(x_1, x_2, x_46);
x_48 = l_Lean_indentExpr(x_47);
x_49 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_48);
lean_ctor_set(x_19, 0, x_49);
x_50 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_19);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_51, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_52;
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_dec(x_56);
x_57 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_55, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 6)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_33, 1);
lean_inc(x_61);
lean_dec(x_33);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_36);
x_63 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_62);
x_64 = lean_mk_array(x_62, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_sub(x_62, x_65);
lean_dec(x_62);
x_67 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_64, x_66);
x_68 = lean_array_get_size(x_67);
x_69 = lean_nat_dec_eq(x_61, x_68);
lean_dec(x_68);
lean_dec(x_61);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_67);
lean_dec(x_60);
lean_dec(x_18);
x_70 = l_Lean_Expr_fvar___override(x_3);
x_71 = l_Lean_Expr_proj___override(x_1, x_2, x_70);
x_72 = l_Lean_indentExpr(x_71);
x_73 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_72);
lean_ctor_set(x_45, 0, x_73);
x_74 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_74);
lean_ctor_set(x_19, 0, x_45);
x_75 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_free_object(x_19);
x_76 = lean_ctor_get(x_60, 0);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Expr_const___override(x_77, x_18);
x_79 = l_Lean_mkAppN(x_78, x_67);
lean_dec(x_67);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_80 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_79, x_4, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_box(0);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 1, x_81);
lean_ctor_set(x_45, 0, x_83);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_84 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(x_1, x_2, x_3, x_83, x_2, x_36, x_2, x_65, x_45, x_4, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_box(0);
x_90 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_88, x_3, x_1, x_2, x_89, x_4, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_88);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_84, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_86, 0);
lean_inc(x_93);
lean_dec(x_86);
lean_ctor_set(x_84, 0, x_93);
return x_84;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_dec(x_84);
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
lean_dec(x_86);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
return x_84;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_84, 0);
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_84);
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
lean_free_object(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_80);
if (x_101 == 0)
{
return x_80;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_80, 0);
x_103 = lean_ctor_get(x_80, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_80);
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
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_58);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_14);
x_105 = lean_ctor_get(x_57, 1);
lean_inc(x_105);
lean_dec(x_57);
x_106 = l_Lean_Expr_fvar___override(x_3);
x_107 = l_Lean_Expr_proj___override(x_1, x_2, x_106);
x_108 = l_Lean_indentExpr(x_107);
x_109 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_108);
lean_ctor_set(x_45, 0, x_109);
x_110 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_110);
lean_ctor_set(x_19, 0, x_45);
x_111 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_free_object(x_45);
lean_dec(x_33);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_57);
if (x_112 == 0)
{
return x_57;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_57, 0);
x_114 = lean_ctor_get(x_57, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_57);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_45, 0);
lean_inc(x_116);
lean_dec(x_45);
x_117 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_116, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 6)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_33, 1);
lean_inc(x_121);
lean_dec(x_33);
x_122 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_36);
x_123 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_122);
x_124 = lean_mk_array(x_122, x_123);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_sub(x_122, x_125);
lean_dec(x_122);
x_127 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_124, x_126);
x_128 = lean_array_get_size(x_127);
x_129 = lean_nat_dec_eq(x_121, x_128);
lean_dec(x_128);
lean_dec(x_121);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_127);
lean_dec(x_120);
lean_dec(x_18);
x_130 = l_Lean_Expr_fvar___override(x_3);
x_131 = l_Lean_Expr_proj___override(x_1, x_2, x_130);
x_132 = l_Lean_indentExpr(x_131);
x_133 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_135);
lean_ctor_set(x_19, 0, x_134);
x_136 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_free_object(x_19);
x_137 = lean_ctor_get(x_120, 0);
lean_inc(x_137);
lean_dec(x_120);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = l_Lean_Expr_const___override(x_138, x_18);
x_140 = l_Lean_mkAppN(x_139, x_127);
lean_dec(x_127);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_141 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_140, x_4, x_5, x_6, x_7, x_8, x_119);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_146 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(x_1, x_2, x_3, x_144, x_2, x_36, x_2, x_125, x_145, x_4, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_box(0);
x_152 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_150, x_3, x_1, x_2, x_151, x_4, x_5, x_6, x_7, x_8, x_149);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_154 = x_146;
} else {
 lean_dec_ref(x_146);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_148, 0);
lean_inc(x_155);
lean_dec(x_148);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_ctor_get(x_146, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_146, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_159 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_141, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_141, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_163 = x_141;
} else {
 lean_dec_ref(x_141);
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
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_118);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_14);
x_165 = lean_ctor_get(x_117, 1);
lean_inc(x_165);
lean_dec(x_117);
x_166 = l_Lean_Expr_fvar___override(x_3);
x_167 = l_Lean_Expr_proj___override(x_1, x_2, x_166);
x_168 = l_Lean_indentExpr(x_167);
x_169 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_171);
lean_ctor_set(x_19, 0, x_170);
x_172 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_19, x_4, x_5, x_6, x_7, x_8, x_165);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_33);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_117, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_117, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_175 = x_117;
} else {
 lean_dec_ref(x_117);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_33);
lean_free_object(x_19);
lean_dec(x_18);
lean_dec(x_14);
x_177 = !lean_is_exclusive(x_45);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_178 = lean_ctor_get(x_45, 1);
lean_dec(x_178);
x_179 = lean_ctor_get(x_45, 0);
lean_dec(x_179);
x_180 = !lean_is_exclusive(x_53);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_53, 1);
lean_dec(x_181);
x_182 = lean_ctor_get(x_53, 0);
lean_dec(x_182);
x_183 = l_Lean_Expr_fvar___override(x_3);
x_184 = l_Lean_Expr_proj___override(x_1, x_2, x_183);
x_185 = l_Lean_indentExpr(x_184);
x_186 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_53, 7);
lean_ctor_set(x_53, 1, x_185);
lean_ctor_set(x_53, 0, x_186);
x_187 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_187);
lean_ctor_set(x_45, 0, x_53);
x_188 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_45, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_53);
x_189 = l_Lean_Expr_fvar___override(x_3);
x_190 = l_Lean_Expr_proj___override(x_1, x_2, x_189);
x_191 = l_Lean_indentExpr(x_190);
x_192 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_194);
lean_ctor_set(x_45, 0, x_193);
x_195 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_45, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_45);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_196 = x_53;
} else {
 lean_dec_ref(x_53);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Expr_fvar___override(x_3);
x_198 = l_Lean_Expr_proj___override(x_1, x_2, x_197);
x_199 = l_Lean_indentExpr(x_198);
x_200 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(7, 2, 0);
} else {
 x_201 = x_196;
 lean_ctor_set_tag(x_201, 7);
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_203, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_204;
}
}
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_14);
x_205 = l_Lean_Expr_fvar___override(x_3);
x_206 = l_Lean_Expr_proj___override(x_1, x_2, x_205);
x_207 = l_Lean_indentExpr(x_206);
x_208 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_207);
lean_ctor_set(x_19, 0, x_208);
x_209 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_19);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_210, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_14);
x_212 = l_Lean_Expr_fvar___override(x_3);
x_213 = l_Lean_Expr_proj___override(x_1, x_2, x_212);
x_214 = l_Lean_indentExpr(x_213);
x_215 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_214);
lean_ctor_set(x_19, 0, x_215);
x_216 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_19);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_217, x_4, x_5, x_6, x_7, x_8, x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_19, 0);
x_220 = lean_ctor_get(x_19, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_19);
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = lean_environment_find(x_221, x_17);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_18);
lean_dec(x_14);
x_223 = l_Lean_Expr_fvar___override(x_3);
x_224 = l_Lean_Expr_proj___override(x_1, x_2, x_223);
x_225 = l_Lean_indentExpr(x_224);
x_226 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_225);
x_228 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_229, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_230;
}
else
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_222, 0);
lean_inc(x_231);
lean_dec(x_222);
if (lean_obj_tag(x_231) == 5)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = lean_ctor_get_uint8(x_232, sizeof(void*)*6);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_232, 2);
lean_inc(x_234);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_nat_dec_eq(x_234, x_235);
lean_dec(x_234);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
x_237 = l_Lean_Expr_fvar___override(x_3);
x_238 = l_Lean_Expr_proj___override(x_1, x_2, x_237);
x_239 = l_Lean_indentExpr(x_238);
x_240 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_243 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_243, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_244;
}
else
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_232, 4);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
x_246 = l_Lean_Expr_fvar___override(x_3);
x_247 = l_Lean_Expr_proj___override(x_1, x_2, x_246);
x_248 = l_Lean_indentExpr(x_247);
x_249 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_252, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_253;
}
else
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_245, 1);
lean_inc(x_254);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_245, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_256 = x_245;
} else {
 lean_dec_ref(x_245);
 x_256 = lean_box(0);
}
x_257 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_255, x_4, x_5, x_6, x_7, x_8, x_220);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 6)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_232, 1);
lean_inc(x_261);
lean_dec(x_232);
x_262 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_14, x_235);
x_263 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_262);
x_264 = lean_mk_array(x_262, x_263);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_sub(x_262, x_265);
lean_dec(x_262);
x_267 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_264, x_266);
x_268 = lean_array_get_size(x_267);
x_269 = lean_nat_dec_eq(x_261, x_268);
lean_dec(x_268);
lean_dec(x_261);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_267);
lean_dec(x_260);
lean_dec(x_18);
x_270 = l_Lean_Expr_fvar___override(x_3);
x_271 = l_Lean_Expr_proj___override(x_1, x_2, x_270);
x_272 = l_Lean_indentExpr(x_271);
x_273 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_256)) {
 x_274 = lean_alloc_ctor(7, 2, 0);
} else {
 x_274 = x_256;
 lean_ctor_set_tag(x_274, 7);
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
x_275 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_276, x_4, x_5, x_6, x_7, x_8, x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_278 = lean_ctor_get(x_260, 0);
lean_inc(x_278);
lean_dec(x_260);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Lean_Expr_const___override(x_279, x_18);
x_281 = l_Lean_mkAppN(x_280, x_267);
lean_dec(x_267);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_282 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_281, x_4, x_5, x_6, x_7, x_8, x_259);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_256;
 lean_ctor_set_tag(x_286, 0);
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_287 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(x_1, x_2, x_3, x_285, x_2, x_235, x_2, x_265, x_286, x_4, x_5, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
lean_dec(x_287);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_box(0);
x_293 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_291, x_3, x_1, x_2, x_292, x_4, x_5, x_6, x_7, x_8, x_290);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_291);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_288);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_295 = x_287;
} else {
 lean_dec_ref(x_287);
 x_295 = lean_box(0);
}
x_296 = lean_ctor_get(x_289, 0);
lean_inc(x_296);
lean_dec(x_289);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_294);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_298 = lean_ctor_get(x_287, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_287, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_300 = x_287;
} else {
 lean_dec_ref(x_287);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = lean_ctor_get(x_282, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_282, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_304 = x_282;
} else {
 lean_dec_ref(x_282);
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
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_258);
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
x_306 = lean_ctor_get(x_257, 1);
lean_inc(x_306);
lean_dec(x_257);
x_307 = l_Lean_Expr_fvar___override(x_3);
x_308 = l_Lean_Expr_proj___override(x_1, x_2, x_307);
x_309 = l_Lean_indentExpr(x_308);
x_310 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_256)) {
 x_311 = lean_alloc_ctor(7, 2, 0);
} else {
 x_311 = x_256;
 lean_ctor_set_tag(x_311, 7);
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
x_312 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_313, x_4, x_5, x_6, x_7, x_8, x_306);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_256);
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_315 = lean_ctor_get(x_257, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_257, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_317 = x_257;
} else {
 lean_dec_ref(x_257);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_319 = x_245;
} else {
 lean_dec_ref(x_245);
 x_319 = lean_box(0);
}
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_320 = x_254;
} else {
 lean_dec_ref(x_254);
 x_320 = lean_box(0);
}
x_321 = l_Lean_Expr_fvar___override(x_3);
x_322 = l_Lean_Expr_proj___override(x_1, x_2, x_321);
x_323 = l_Lean_indentExpr(x_322);
x_324 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_320)) {
 x_325 = lean_alloc_ctor(7, 2, 0);
} else {
 x_325 = x_320;
 lean_ctor_set_tag(x_325, 7);
}
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
if (lean_is_scalar(x_319)) {
 x_327 = lean_alloc_ctor(7, 2, 0);
} else {
 x_327 = x_319;
 lean_ctor_set_tag(x_327, 7);
}
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_327, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_328;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_14);
x_329 = l_Lean_Expr_fvar___override(x_3);
x_330 = l_Lean_Expr_proj___override(x_1, x_2, x_329);
x_331 = l_Lean_indentExpr(x_330);
x_332 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_333 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_335, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_14);
x_337 = l_Lean_Expr_fvar___override(x_3);
x_338 = l_Lean_Expr_proj___override(x_1, x_2, x_337);
x_339 = l_Lean_indentExpr(x_338);
x_340 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_339);
x_342 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_343, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_344;
}
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_16);
lean_dec(x_14);
x_345 = l_Lean_Expr_fvar___override(x_3);
x_346 = l_Lean_Expr_proj___override(x_1, x_2, x_345);
x_347 = l_Lean_indentExpr(x_346);
x_348 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
x_350 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_351 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_351, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_352;
}
}
else
{
lean_object* x_353; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_10, 0, x_353);
return x_10;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = lean_ctor_get(x_10, 0);
x_355 = lean_ctor_get(x_10, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_10);
x_356 = l_Lean_Expr_headBeta(x_354);
x_357 = l_Lean_Expr_isErased(x_356);
if (x_357 == 0)
{
lean_object* x_358; 
x_358 = l_Lean_Expr_getAppFn(x_356);
if (lean_obj_tag(x_358) == 4)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_st_ref_get(x_8, x_355);
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_364 = x_361;
} else {
 lean_dec_ref(x_361);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_362, 0);
lean_inc(x_365);
lean_dec(x_362);
x_366 = lean_environment_find(x_365, x_359);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_360);
lean_dec(x_356);
x_367 = l_Lean_Expr_fvar___override(x_3);
x_368 = l_Lean_Expr_proj___override(x_1, x_2, x_367);
x_369 = l_Lean_indentExpr(x_368);
x_370 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(7, 2, 0);
} else {
 x_371 = x_364;
 lean_ctor_set_tag(x_371, 7);
}
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_373, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_374;
}
else
{
lean_object* x_375; 
x_375 = lean_ctor_get(x_366, 0);
lean_inc(x_375);
lean_dec(x_366);
if (lean_obj_tag(x_375) == 5)
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec(x_375);
x_377 = lean_ctor_get_uint8(x_376, sizeof(void*)*6);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_378 = lean_ctor_get(x_376, 2);
lean_inc(x_378);
x_379 = lean_unsigned_to_nat(0u);
x_380 = lean_nat_dec_eq(x_378, x_379);
lean_dec(x_378);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_376);
lean_dec(x_360);
lean_dec(x_356);
x_381 = l_Lean_Expr_fvar___override(x_3);
x_382 = l_Lean_Expr_proj___override(x_1, x_2, x_381);
x_383 = l_Lean_indentExpr(x_382);
x_384 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_364)) {
 x_385 = lean_alloc_ctor(7, 2, 0);
} else {
 x_385 = x_364;
 lean_ctor_set_tag(x_385, 7);
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_387 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_387, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_376, 4);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_376);
lean_dec(x_360);
lean_dec(x_356);
x_390 = l_Lean_Expr_fvar___override(x_3);
x_391 = l_Lean_Expr_proj___override(x_1, x_2, x_390);
x_392 = l_Lean_indentExpr(x_391);
x_393 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_364)) {
 x_394 = lean_alloc_ctor(7, 2, 0);
} else {
 x_394 = x_364;
 lean_ctor_set_tag(x_394, 7);
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_392);
x_395 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_396, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_397;
}
else
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_389, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_400 = x_389;
} else {
 lean_dec_ref(x_389);
 x_400 = lean_box(0);
}
x_401 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_399, x_4, x_5, x_6, x_7, x_8, x_363);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
if (lean_obj_tag(x_402) == 6)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_ctor_get(x_376, 1);
lean_inc(x_405);
lean_dec(x_376);
x_406 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_356, x_379);
x_407 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1;
lean_inc(x_406);
x_408 = lean_mk_array(x_406, x_407);
x_409 = lean_unsigned_to_nat(1u);
x_410 = lean_nat_sub(x_406, x_409);
lean_dec(x_406);
x_411 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_356, x_408, x_410);
x_412 = lean_array_get_size(x_411);
x_413 = lean_nat_dec_eq(x_405, x_412);
lean_dec(x_412);
lean_dec(x_405);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_411);
lean_dec(x_404);
lean_dec(x_360);
x_414 = l_Lean_Expr_fvar___override(x_3);
x_415 = l_Lean_Expr_proj___override(x_1, x_2, x_414);
x_416 = l_Lean_indentExpr(x_415);
x_417 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_400)) {
 x_418 = lean_alloc_ctor(7, 2, 0);
} else {
 x_418 = x_400;
 lean_ctor_set_tag(x_418, 7);
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_416);
x_419 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
if (lean_is_scalar(x_364)) {
 x_420 = lean_alloc_ctor(7, 2, 0);
} else {
 x_420 = x_364;
 lean_ctor_set_tag(x_420, 7);
}
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_420, x_4, x_5, x_6, x_7, x_8, x_403);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_364);
x_422 = lean_ctor_get(x_404, 0);
lean_inc(x_422);
lean_dec(x_404);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec(x_422);
x_424 = l_Lean_Expr_const___override(x_423, x_360);
x_425 = l_Lean_mkAppN(x_424, x_411);
lean_dec(x_411);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_426 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_425, x_4, x_5, x_6, x_7, x_8, x_403);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_box(0);
if (lean_is_scalar(x_400)) {
 x_430 = lean_alloc_ctor(0, 2, 0);
} else {
 x_430 = x_400;
 lean_ctor_set_tag(x_430, 0);
}
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_427);
lean_inc(x_3);
lean_inc_n(x_2, 2);
lean_inc(x_1);
x_431 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(x_1, x_2, x_3, x_429, x_2, x_379, x_2, x_409, x_430, x_4, x_5, x_6, x_7, x_8, x_428);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_434 = lean_ctor_get(x_431, 1);
lean_inc(x_434);
lean_dec(x_431);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
lean_dec(x_432);
x_436 = lean_box(0);
x_437 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_435, x_3, x_1, x_2, x_436, x_4, x_5, x_6, x_7, x_8, x_434);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_435);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_432);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_438 = lean_ctor_get(x_431, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_439 = x_431;
} else {
 lean_dec_ref(x_431);
 x_439 = lean_box(0);
}
x_440 = lean_ctor_get(x_433, 0);
lean_inc(x_440);
lean_dec(x_433);
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_438);
return x_441;
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_ctor_get(x_431, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_431, 1);
lean_inc(x_443);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_444 = x_431;
} else {
 lean_dec_ref(x_431);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_400);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_446 = lean_ctor_get(x_426, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_426, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_448 = x_426;
} else {
 lean_dec_ref(x_426);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
return x_449;
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_402);
lean_dec(x_376);
lean_dec(x_360);
lean_dec(x_356);
x_450 = lean_ctor_get(x_401, 1);
lean_inc(x_450);
lean_dec(x_401);
x_451 = l_Lean_Expr_fvar___override(x_3);
x_452 = l_Lean_Expr_proj___override(x_1, x_2, x_451);
x_453 = l_Lean_indentExpr(x_452);
x_454 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_400)) {
 x_455 = lean_alloc_ctor(7, 2, 0);
} else {
 x_455 = x_400;
 lean_ctor_set_tag(x_455, 7);
}
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_453);
x_456 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
if (lean_is_scalar(x_364)) {
 x_457 = lean_alloc_ctor(7, 2, 0);
} else {
 x_457 = x_364;
 lean_ctor_set_tag(x_457, 7);
}
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
x_458 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_457, x_4, x_5, x_6, x_7, x_8, x_450);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_400);
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_360);
lean_dec(x_356);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_459 = lean_ctor_get(x_401, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_401, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_461 = x_401;
} else {
 lean_dec_ref(x_401);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_376);
lean_dec(x_364);
lean_dec(x_360);
lean_dec(x_356);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_463 = x_389;
} else {
 lean_dec_ref(x_389);
 x_463 = lean_box(0);
}
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_464 = x_398;
} else {
 lean_dec_ref(x_398);
 x_464 = lean_box(0);
}
x_465 = l_Lean_Expr_fvar___override(x_3);
x_466 = l_Lean_Expr_proj___override(x_1, x_2, x_465);
x_467 = l_Lean_indentExpr(x_466);
x_468 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_464)) {
 x_469 = lean_alloc_ctor(7, 2, 0);
} else {
 x_469 = x_464;
 lean_ctor_set_tag(x_469, 7);
}
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_467);
x_470 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
if (lean_is_scalar(x_463)) {
 x_471 = lean_alloc_ctor(7, 2, 0);
} else {
 x_471 = x_463;
 lean_ctor_set_tag(x_471, 7);
}
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_471, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_472;
}
}
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
lean_dec(x_376);
lean_dec(x_360);
lean_dec(x_356);
x_473 = l_Lean_Expr_fvar___override(x_3);
x_474 = l_Lean_Expr_proj___override(x_1, x_2, x_473);
x_475 = l_Lean_indentExpr(x_474);
x_476 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_364)) {
 x_477 = lean_alloc_ctor(7, 2, 0);
} else {
 x_477 = x_364;
 lean_ctor_set_tag(x_477, 7);
}
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_479 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
x_480 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_479, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_480;
}
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_375);
lean_dec(x_360);
lean_dec(x_356);
x_481 = l_Lean_Expr_fvar___override(x_3);
x_482 = l_Lean_Expr_proj___override(x_1, x_2, x_481);
x_483 = l_Lean_indentExpr(x_482);
x_484 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
if (lean_is_scalar(x_364)) {
 x_485 = lean_alloc_ctor(7, 2, 0);
} else {
 x_485 = x_364;
 lean_ctor_set_tag(x_485, 7);
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_483);
x_486 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_487 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
x_488 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_487, x_4, x_5, x_6, x_7, x_8, x_363);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_488;
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_358);
lean_dec(x_356);
x_489 = l_Lean_Expr_fvar___override(x_3);
x_490 = l_Lean_Expr_proj___override(x_1, x_2, x_489);
x_491 = l_Lean_indentExpr(x_490);
x_492 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2;
x_493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
x_494 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_495 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
x_496 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_495, x_4, x_5, x_6, x_7, x_8, x_355);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; 
lean_dec(x_356);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = l_Lean_Compiler_LCNF_erasedExpr;
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_355);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_499 = !lean_is_exclusive(x_10);
if (x_499 == 0)
{
return x_10;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_10, 0);
x_501 = lean_ctor_get(x_10, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_10);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_InferType_inferProjType___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLetValueType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_InferType_inferLitValueType(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_erasedExpr;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_InferType_inferProjType(x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_Compiler_LCNF_InferType_inferConstType(x_17, x_18, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_2);
x_30 = l_Lean_Compiler_LCNF_InferType_getType(x_28, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_31, x_29, x_2, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_9 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_inferAppType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_20);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_28);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
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
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
x_41 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_inc(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getLevel___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Compiler_LCNF_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 3)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = l_Lean_Expr_isErased(x_8);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
x_19 = l_Lean_indentExpr(x_1);
x_20 = l_Lean_Compiler_LCNF_getLevel___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_23, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l_Lean_levelOne;
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = l_Lean_Expr_isErased(x_8);
lean_dec(x_8);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_indentExpr(x_1);
x_29 = l_Lean_Compiler_LCNF_getLevel___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_32, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_Lean_levelOne;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_getLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_8 = l_Lean_Compiler_LCNF_InferType_inferArgType(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_8 = l_Lean_Compiler_LCNF_InferType_inferLetValueType(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Compiler_LCNF_getType(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_13 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_10, x_8, x_12, x_2, x_3, x_4, x_5, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
case 5:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Compiler_LCNF_getType(x_21, x_2, x_3, x_4, x_5, x_6);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
default: 
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_1 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Code_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_inferType(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_size(x_1);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Compiler_LCNF_InferType_mkForallParams___spec__1(x_11, x_12, x_1);
x_14 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_15 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_13, x_9, x_14, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_9);
lean_dec(x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Code_inferParamType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_AltCore_getCode(x_1);
x_8 = l_Lean_Compiler_LCNF_Code_inferType(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_AltCore_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Compiler_LCNF_mkLetDecl(x_9, x_12, x_1, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6;
x_9 = l_Lean_Compiler_LCNF_InferType_mkForallParams(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_mkForallParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_Compiler_LCNF_Code_inferType(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_mkForallParams(x_1, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_mkFreshBinderName(x_3, x_4, x_5, x_6, x_7, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_mkFunDecl(x_16, x_13, x_1, x_2, x_4, x_5, x_6, x_7, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = l_Lean_Compiler_LCNF_AltCore_inferType(x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Compiler_LCNF_joinTypes(x_4, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = lean_st_ref_get(x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_3, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_4, 2);
x_19 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_20);
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_8);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_4, 2);
x_27 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_tag(x_8, 3);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_8, 0, x_28);
lean_inc(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_3, x_32);
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
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
x_41 = l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1;
lean_inc(x_40);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
lean_ctor_set(x_42, 3, x_40);
x_43 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_1);
lean_inc(x_7);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_37)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_37;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_2 = l_Lean_Compiler_LCNF_instInhabitedAltCore___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_array_get_size(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_lt(x_34, x_33);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1;
x_37 = l_outOfBounds___rarg(x_36);
x_8 = x_37;
goto block_32;
}
else
{
lean_object* x_38; 
x_38 = lean_array_fget(x_1, x_34);
x_8 = x_38;
goto block_32;
}
block_32:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_AltCore_inferType(x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_1);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Array_toSubarray___rarg(x_1, x_13, x_12);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1(x_14, x_16, x_18, x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`Code.bind` failed, empty `cases` found", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___rarg(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
x_11 = l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2(x_10, x_2, x_3, x_4, x_5, x_6);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Compiler_LCNF_mkCasesResultType___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Compiler_LCNF_mkCasesResultType___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_mkCasesResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabitedOfMonad___rarg(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.isErasedCompatible.go", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
x_2 = l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
x_3 = lean_unsigned_to_nat(314u);
x_4 = lean_unsigned_to_nat(50u);
x_5 = l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_sub(x_10, x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_14 = lean_nat_dec_lt(x_13, x_10);
lean_dec(x_10);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_2);
x_15 = l_instInhabitedBool;
x_16 = lean_box(x_15);
x_17 = l_outOfBounds___rarg(x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_array_fget(x_2, x_13);
lean_dec(x_13);
lean_dec(x_2);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = l_Lean_Compiler_LCNF_getType(x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Compiler_LCNF_isPredicateType(x_28);
x_30 = lean_box(x_29);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Compiler_LCNF_isPredicateType(x_31);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
case 3:
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
return x_42;
}
case 4:
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = l_Lean_Expr_isErased(x_8);
lean_dec(x_8);
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
case 5:
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
lean_dec(x_8);
x_1 = x_46;
goto _start;
}
case 6:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_8, 2);
lean_inc(x_49);
lean_dec(x_8);
x_50 = l_Lean_Compiler_LCNF_isPredicateType(x_48);
x_51 = lean_box(x_50);
x_52 = lean_array_push(x_2, x_51);
x_1 = x_49;
x_2 = x_52;
goto _start;
}
case 7:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 2);
lean_inc(x_55);
lean_dec(x_8);
x_56 = l_Lean_Compiler_LCNF_isPredicateType(x_54);
x_57 = lean_box(x_56);
x_58 = lean_array_push(x_2, x_57);
x_1 = x_55;
x_2 = x_58;
goto _start;
}
case 10:
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_dec(x_8);
x_1 = x_60;
goto _start;
}
default: 
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_8);
lean_dec(x_2);
x_62 = l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2;
x_63 = l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1(x_62, x_3, x_4, x_5, x_6, x_7);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_isErasedCompatible_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Level_isEquiv(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_56; 
x_56 = lean_expr_eqv(x_1, x_2);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_isErased(x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_inc(x_1);
x_58 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_59 = l_Lean_Expr_headBeta(x_2);
x_60 = lean_expr_eqv(x_1, x_58);
if (x_60 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_58;
x_2 = x_59;
goto _start;
}
else
{
uint8_t x_62; 
x_62 = lean_expr_eqv(x_2, x_59);
if (x_62 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_58;
x_2 = x_59;
goto _start;
}
else
{
lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_58);
x_64 = lean_box(0);
x_3 = x_64;
goto block_55;
}
}
}
else
{
uint8_t x_65; 
x_65 = l_Lean_Expr_isErased(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_inc(x_1);
x_66 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_67 = l_Lean_Expr_headBeta(x_2);
x_68 = lean_expr_eqv(x_1, x_66);
if (x_68 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_66;
x_2 = x_67;
goto _start;
}
else
{
uint8_t x_70; 
x_70 = lean_expr_eqv(x_2, x_67);
if (x_70 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_66;
x_2 = x_67;
goto _start;
}
else
{
lean_object* x_72; 
lean_dec(x_67);
lean_dec(x_66);
x_72 = lean_box(0);
x_3 = x_72;
goto block_55;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = 1;
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_74 = 1;
return x_74;
}
block_55:
{
lean_dec(x_3);
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Level_isEquiv(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
case 10:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_2 = x_7;
goto _start;
}
default: 
{
uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_name_eq(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_13);
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
return x_16;
}
}
case 10:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_2 = x_17;
goto _start;
}
default: 
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = 0;
return x_19;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_Compiler_LCNF_eqvTypes(x_20, x_22);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_23);
lean_dec(x_21);
x_25 = 0;
return x_25;
}
else
{
x_1 = x_21;
x_2 = x_23;
goto _start;
}
}
case 10:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_2 = x_27;
goto _start;
}
default: 
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
return x_29;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lean_Compiler_LCNF_eqvTypes(x_30, x_32);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_33);
lean_dec(x_31);
x_35 = 0;
return x_35;
}
else
{
x_1 = x_31;
x_2 = x_33;
goto _start;
}
}
case 10:
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_2 = x_37;
goto _start;
}
default: 
{
uint8_t x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
return x_39;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_Compiler_LCNF_eqvTypes(x_40, x_42);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_43);
lean_dec(x_41);
x_45 = 0;
return x_45;
}
else
{
x_1 = x_41;
x_2 = x_43;
goto _start;
}
}
case 10:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_dec(x_2);
x_2 = x_47;
goto _start;
}
default: 
{
uint8_t x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = 0;
return x_49;
}
}
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_dec(x_1);
x_1 = x_50;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_dec(x_2);
x_2 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = 0;
return x_54;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isEqv___at_Lean_Compiler_LCNF_eqvTypes___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_eqvTypes(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_OtherDecl(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_OtherDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__1);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__2);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__3);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__4);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__5);
l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___closed__6);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6);
l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__3);
l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4 = _init_l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_InferType_inferType___spec__1___closed__4);
l_Lean_Compiler_LCNF_InferType_inferType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferType___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__3);
l_Lean_Compiler_LCNF_InferType_inferType___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__4);
l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Compiler_LCNF_InferType_inferForallType_go___spec__1___closed__1);
l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferAppType___closed__1);
l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1 = _init_l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1();
lean_mark_persistent(l_Lean_throwError___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__1___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__1);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__2);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__3);
l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__2___closed__4);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__1);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__2);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__3);
l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Compiler_LCNF_InferType_inferProjType___spec__5___lambda__1___closed__4);
l_Lean_Compiler_LCNF_getLevel___closed__1 = _init_l_Lean_Compiler_LCNF_getLevel___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getLevel___closed__1);
l_Lean_Compiler_LCNF_getLevel___closed__2 = _init_l_Lean_Compiler_LCNF_getLevel___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_getLevel___closed__2);
l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___lambda__1___closed__1);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__1 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__2 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_isErasedCompatible_go___spec__1___closed__2);
l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1 = _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2 = _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
