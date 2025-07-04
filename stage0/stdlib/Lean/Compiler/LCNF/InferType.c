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
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0;
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Nat_decLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__1;
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___boxed(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0;
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__2(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt;
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3;
lean_object* l_Std_Iterators_instIteratorMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getLevel___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_getLevel___closed__0;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__11;
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_InferType_inferType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4;
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15;
LEAN_EXPORT lean_object* l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__13;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
uint8_t l_Lean_Expr_isErased(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PRange_instUpwardEnumerableNat;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l_Lean_Expr_isAny(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferParamType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__5;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_eqvTypes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadNameGeneratorCoreM;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__7;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__8;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1;
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__10;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLetValueType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__15;
lean_object* l_Lean_monadNameGeneratorLift___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0;
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__9;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3;
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__14;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8;
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
lean_object* l_Lean_Level_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_inferType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__6;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0;
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1;
static lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___closed__0;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18;
static lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_local_ctx_find(x_2, x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_1, x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_getBinderName___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_getBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_getBinderName___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
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
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
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
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_2, x_10);
if (x_11 == 1)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_15 = lean_array_fget(x_1, x_14);
x_16 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_4);
lean_inc(x_16);
x_17 = l_Lean_Compiler_LCNF_InferType_getBinderName___redArg(x_16, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_4);
x_20 = l_Lean_Compiler_LCNF_InferType_getType(x_16, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_expr_abstract_range(x_21, x_14, x_1);
lean_dec(x_21);
x_24 = 0;
x_25 = l_Lean_Expr_forallE___override(x_18, x_23, x_3, x_24);
x_2 = x_14;
x_3 = x_25;
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_18);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_2 = x_14;
x_3 = x_27;
x_9 = x_28;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_4);
return x_20;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_abstract(x_2, x_1);
x_10 = lean_array_get_size(x_1);
x_11 = l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg(x_1, x_10, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldRevM_loop___at___Lean_Compiler_LCNF_InferType_mkForallFVars_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = l_Lean_Expr_fvar___override(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2;
x_4 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4;
x_3 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(x_8, x_9, x_1);
x_11 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_10, x_2, x_11, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Core_instMonadNameGeneratorCoreM;
x_2 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7;
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8;
x_2 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6;
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9;
x_2 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6;
x_3 = l_Lean_monadNameGeneratorLift___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1;
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 4);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_22 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_16);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_24, 0, x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_18);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_28, 0, x_17);
lean_ctor_set(x_13, 4, x_26);
lean_ctor_set(x_13, 3, x_27);
lean_ctor_set(x_13, 2, x_28);
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_25);
lean_ctor_set(x_11, 1, x_22);
x_29 = l_ReaderT_instMonad___redArg(x_11);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_38 = lean_ctor_get(x_31, 1);
lean_dec(x_38);
x_39 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_40 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_34);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_45, 0, x_36);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_46, 0, x_35);
lean_ctor_set(x_31, 4, x_44);
lean_ctor_set(x_31, 3, x_45);
lean_ctor_set(x_31, 2, x_46);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_43);
lean_ctor_set(x_29, 1, x_40);
x_47 = l_ReaderT_instMonad___redArg(x_29);
x_48 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_49 = l_Lean_mkFreshFVarId___redArg(x_47, x_48);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = lean_apply_6(x_49, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_51);
x_53 = l_Lean_Expr_fvar___override(x_51);
x_54 = 0;
x_55 = l_Lean_LocalContext_mkLocalDecl(x_5, x_51, x_1, x_2, x_3, x_54);
x_56 = lean_apply_7(x_4, x_53, x_55, x_6, x_7, x_8, x_9, x_52);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_50, 0);
x_59 = lean_ctor_get(x_50, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_50);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_61 = lean_ctor_get(x_31, 0);
x_62 = lean_ctor_get(x_31, 2);
x_63 = lean_ctor_get(x_31, 3);
x_64 = lean_ctor_get(x_31, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_31);
x_65 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_66 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_61);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_67, 0, x_61);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_70, 0, x_64);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_72, 0, x_62);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_29, 1, x_66);
lean_ctor_set(x_29, 0, x_73);
x_74 = l_ReaderT_instMonad___redArg(x_29);
x_75 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_76 = l_Lean_mkFreshFVarId___redArg(x_74, x_75);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = lean_apply_6(x_76, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_78);
x_80 = l_Lean_Expr_fvar___override(x_78);
x_81 = 0;
x_82 = l_Lean_LocalContext_mkLocalDecl(x_5, x_78, x_1, x_2, x_3, x_81);
x_83 = lean_apply_7(x_4, x_80, x_82, x_6, x_7, x_8, x_9, x_79);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_88 = lean_ctor_get(x_29, 0);
lean_inc(x_88);
lean_dec(x_29);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 4);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
x_94 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_95 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_97, 0, x_89);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_99, 0, x_92);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_100, 0, x_91);
x_101 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_101, 0, x_90);
if (lean_is_scalar(x_93)) {
 x_102 = lean_alloc_ctor(0, 5, 0);
} else {
 x_102 = x_93;
}
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_94);
lean_ctor_set(x_102, 2, x_101);
lean_ctor_set(x_102, 3, x_100);
lean_ctor_set(x_102, 4, x_99);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_106 = l_Lean_mkFreshFVarId___redArg(x_104, x_105);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_107 = lean_apply_6(x_106, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_108);
x_110 = l_Lean_Expr_fvar___override(x_108);
x_111 = 0;
x_112 = l_Lean_LocalContext_mkLocalDecl(x_5, x_108, x_1, x_2, x_3, x_111);
x_113 = lean_apply_7(x_4, x_110, x_112, x_6, x_7, x_8, x_9, x_109);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_107, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_116 = x_107;
} else {
 lean_dec_ref(x_107);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_118 = lean_ctor_get(x_13, 0);
x_119 = lean_ctor_get(x_13, 2);
x_120 = lean_ctor_get(x_13, 3);
x_121 = lean_ctor_get(x_13, 4);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_13);
x_122 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_123 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_118);
x_124 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_124, 0, x_118);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_125, 0, x_118);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_127, 0, x_121);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_128, 0, x_120);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_129, 0, x_119);
x_130 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_122);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_128);
lean_ctor_set(x_130, 4, x_127);
lean_ctor_set(x_11, 1, x_123);
lean_ctor_set(x_11, 0, x_130);
x_131 = l_ReaderT_instMonad___redArg(x_11);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 4);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
x_139 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_140 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_134);
x_141 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_141, 0, x_134);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_142, 0, x_134);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_144, 0, x_137);
x_145 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_145, 0, x_136);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_146, 0, x_135);
if (lean_is_scalar(x_138)) {
 x_147 = lean_alloc_ctor(0, 5, 0);
} else {
 x_147 = x_138;
}
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_144);
if (lean_is_scalar(x_133)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_133;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
x_149 = l_ReaderT_instMonad___redArg(x_148);
x_150 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_151 = l_Lean_mkFreshFVarId___redArg(x_149, x_150);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_152 = lean_apply_6(x_151, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_153);
x_155 = l_Lean_Expr_fvar___override(x_153);
x_156 = 0;
x_157 = l_Lean_LocalContext_mkLocalDecl(x_5, x_153, x_1, x_2, x_3, x_156);
x_158 = lean_apply_7(x_4, x_155, x_157, x_6, x_7, x_8, x_9, x_154);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_152, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_161 = x_152;
} else {
 lean_dec_ref(x_152);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_163 = lean_ctor_get(x_11, 0);
lean_inc(x_163);
lean_dec(x_11);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_163, 4);
lean_inc(x_167);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 x_168 = x_163;
} else {
 lean_dec_ref(x_163);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_170 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_164);
x_171 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_171, 0, x_164);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_172, 0, x_164);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_174, 0, x_167);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_175, 0, x_166);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_176, 0, x_165);
if (lean_is_scalar(x_168)) {
 x_177 = lean_alloc_ctor(0, 5, 0);
} else {
 x_177 = x_168;
}
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_169);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set(x_177, 4, x_174);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_170);
x_179 = l_ReaderT_instMonad___redArg(x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_180, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 4);
lean_inc(x_185);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 x_186 = x_180;
} else {
 lean_dec_ref(x_180);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_188 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_182);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_189, 0, x_182);
x_190 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_190, 0, x_182);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_192, 0, x_185);
x_193 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_193, 0, x_184);
x_194 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_194, 0, x_183);
if (lean_is_scalar(x_186)) {
 x_195 = lean_alloc_ctor(0, 5, 0);
} else {
 x_195 = x_186;
}
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_187);
lean_ctor_set(x_195, 2, x_194);
lean_ctor_set(x_195, 3, x_193);
lean_ctor_set(x_195, 4, x_192);
if (lean_is_scalar(x_181)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_181;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_188);
x_197 = l_ReaderT_instMonad___redArg(x_196);
x_198 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_199 = l_Lean_mkFreshFVarId___redArg(x_197, x_198);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_200 = lean_apply_6(x_199, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_201);
x_203 = l_Lean_Expr_fvar___override(x_201);
x_204 = 0;
x_205 = l_Lean_LocalContext_mkLocalDecl(x_5, x_201, x_1, x_2, x_3, x_204);
x_206 = lean_apply_7(x_4, x_203, x_205, x_6, x_7, x_8, x_9, x_202);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1;
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_ctor_get(x_14, 3);
x_20 = lean_ctor_get(x_14, 4);
x_21 = lean_ctor_get(x_14, 1);
lean_dec(x_21);
x_22 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_23 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_17);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_20);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_19);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_29, 0, x_18);
lean_ctor_set(x_14, 4, x_27);
lean_ctor_set(x_14, 3, x_28);
lean_ctor_set(x_14, 2, x_29);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_26);
lean_ctor_set(x_12, 1, x_23);
x_30 = l_ReaderT_instMonad___redArg(x_12);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 2);
x_37 = lean_ctor_get(x_32, 3);
x_38 = lean_ctor_get(x_32, 4);
x_39 = lean_ctor_get(x_32, 1);
lean_dec(x_39);
x_40 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_41 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_35);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_35);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_37);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_36);
lean_ctor_set(x_32, 4, x_45);
lean_ctor_set(x_32, 3, x_46);
lean_ctor_set(x_32, 2, x_47);
lean_ctor_set(x_32, 1, x_40);
lean_ctor_set(x_32, 0, x_44);
lean_ctor_set(x_30, 1, x_41);
x_48 = l_ReaderT_instMonad___redArg(x_30);
x_49 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_50 = l_Lean_mkFreshFVarId___redArg(x_48, x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = lean_apply_6(x_50, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = l_Lean_Expr_fvar___override(x_52);
x_55 = 0;
x_56 = l_Lean_LocalContext_mkLocalDecl(x_6, x_52, x_2, x_3, x_4, x_55);
x_57 = lean_apply_7(x_5, x_54, x_56, x_7, x_8, x_9, x_10, x_53);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_32, 0);
x_63 = lean_ctor_get(x_32, 2);
x_64 = lean_ctor_get(x_32, 3);
x_65 = lean_ctor_get(x_32, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_32);
x_66 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_67 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_62);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_68, 0, x_62);
x_69 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_69, 0, x_62);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_71, 0, x_65);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_72, 0, x_64);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_73, 0, x_63);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_66);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_71);
lean_ctor_set(x_30, 1, x_67);
lean_ctor_set(x_30, 0, x_74);
x_75 = l_ReaderT_instMonad___redArg(x_30);
x_76 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_77 = l_Lean_mkFreshFVarId___redArg(x_75, x_76);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_78 = lean_apply_6(x_77, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_79);
x_81 = l_Lean_Expr_fvar___override(x_79);
x_82 = 0;
x_83 = l_Lean_LocalContext_mkLocalDecl(x_6, x_79, x_2, x_3, x_4, x_82);
x_84 = lean_apply_7(x_5, x_81, x_83, x_7, x_8, x_9, x_10, x_80);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_89 = lean_ctor_get(x_30, 0);
lean_inc(x_89);
lean_dec(x_30);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_96 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_90);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_97, 0, x_90);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_98, 0, x_90);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_100, 0, x_93);
x_101 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_101, 0, x_92);
x_102 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_102, 0, x_91);
if (lean_is_scalar(x_94)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_94;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_102);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_96);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_107 = l_Lean_mkFreshFVarId___redArg(x_105, x_106);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_108 = lean_apply_6(x_107, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_109);
x_111 = l_Lean_Expr_fvar___override(x_109);
x_112 = 0;
x_113 = l_Lean_LocalContext_mkLocalDecl(x_6, x_109, x_2, x_3, x_4, x_112);
x_114 = lean_apply_7(x_5, x_111, x_113, x_7, x_8, x_9, x_10, x_110);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_119 = lean_ctor_get(x_14, 0);
x_120 = lean_ctor_get(x_14, 2);
x_121 = lean_ctor_get(x_14, 3);
x_122 = lean_ctor_get(x_14, 4);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_14);
x_123 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_124 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_119);
x_125 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_125, 0, x_119);
x_126 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_126, 0, x_119);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_128, 0, x_122);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_129, 0, x_121);
x_130 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_130, 0, x_120);
x_131 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_123);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set(x_131, 4, x_128);
lean_ctor_set(x_12, 1, x_124);
lean_ctor_set(x_12, 0, x_131);
x_132 = l_ReaderT_instMonad___redArg(x_12);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 4);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
x_140 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_141 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_135);
x_142 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_142, 0, x_135);
x_143 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_143, 0, x_135);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_145, 0, x_138);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_146, 0, x_137);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_147, 0, x_136);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 5, 0);
} else {
 x_148 = x_139;
}
lean_ctor_set(x_148, 0, x_144);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_146);
lean_ctor_set(x_148, 4, x_145);
if (lean_is_scalar(x_134)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_134;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_141);
x_150 = l_ReaderT_instMonad___redArg(x_149);
x_151 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_152 = l_Lean_mkFreshFVarId___redArg(x_150, x_151);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_153 = lean_apply_6(x_152, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_154);
x_156 = l_Lean_Expr_fvar___override(x_154);
x_157 = 0;
x_158 = l_Lean_LocalContext_mkLocalDecl(x_6, x_154, x_2, x_3, x_4, x_157);
x_159 = lean_apply_7(x_5, x_156, x_158, x_7, x_8, x_9, x_10, x_155);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_ctor_get(x_153, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_153, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_162 = x_153;
} else {
 lean_dec_ref(x_153);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_164 = lean_ctor_get(x_12, 0);
lean_inc(x_164);
lean_dec(x_12);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 4);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_171 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_165);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_172, 0, x_165);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_173, 0, x_165);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_175, 0, x_168);
x_176 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_176, 0, x_167);
x_177 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_177, 0, x_166);
if (lean_is_scalar(x_169)) {
 x_178 = lean_alloc_ctor(0, 5, 0);
} else {
 x_178 = x_169;
}
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_178, 2, x_177);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set(x_178, 4, x_175);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_171);
x_180 = l_ReaderT_instMonad___redArg(x_179);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 4);
lean_inc(x_186);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 x_187 = x_181;
} else {
 lean_dec_ref(x_181);
 x_187 = lean_box(0);
}
x_188 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4;
x_189 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5;
lean_inc(x_183);
x_190 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_190, 0, x_183);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_191, 0, x_183);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_193, 0, x_186);
x_194 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_194, 0, x_185);
x_195 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_195, 0, x_184);
if (lean_is_scalar(x_187)) {
 x_196 = lean_alloc_ctor(0, 5, 0);
} else {
 x_196 = x_187;
}
lean_ctor_set(x_196, 0, x_192);
lean_ctor_set(x_196, 1, x_188);
lean_ctor_set(x_196, 2, x_195);
lean_ctor_set(x_196, 3, x_194);
lean_ctor_set(x_196, 4, x_193);
if (lean_is_scalar(x_182)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_182;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_189);
x_198 = l_ReaderT_instMonad___redArg(x_197);
x_199 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10;
x_200 = l_Lean_mkFreshFVarId___redArg(x_198, x_199);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_201 = lean_apply_6(x_200, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_202);
x_204 = l_Lean_Expr_fvar___override(x_202);
x_205 = 0;
x_206 = l_Lean_LocalContext_mkLocalDecl(x_6, x_202, x_2, x_3, x_4, x_205);
x_207 = lean_apply_7(x_5, x_204, x_206, x_7, x_8, x_9, x_10, x_203);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_withLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Compiler_LCNF_InferType_withLocalDecl(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1;
x_8 = lean_name_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_1, x_3, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_getOtherDeclType___redArg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_15, x_2);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Compiler_LCNF_Decl_instantiateTypeLevelParams(x_18, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l_Lean_Compiler_LCNF_erasedExpr;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferConstType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferConstType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("String", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt64", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("USize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLitValueType(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__2;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__5;
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8;
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11;
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14;
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17;
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20;
return x_8;
}
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_st_ref_take(x_1, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_11, 2);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_16);
lean_ctor_set(x_11, 2, x_5);
x_17 = lean_st_ref_set(x_1, x_11, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Lean_Name_num___override(x_8, x_9);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Name_num___override(x_8, x_9);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
x_28 = lean_ctor_get(x_11, 5);
x_29 = lean_ctor_get(x_11, 6);
x_30 = lean_ctor_get(x_11, 7);
x_31 = lean_ctor_get(x_11, 8);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_9, x_32);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_33);
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_34, 2, x_5);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set(x_34, 4, x_27);
lean_ctor_set(x_34, 5, x_28);
lean_ctor_set(x_34, 6, x_29);
lean_ctor_set(x_34, 7, x_30);
lean_ctor_set(x_34, 8, x_31);
x_35 = lean_st_ref_set(x_1, x_34, x_12);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = l_Lean_Name_num___override(x_8, x_9);
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
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
x_42 = lean_st_ref_take(x_1, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_43, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_43, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 7);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 8);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 lean_ctor_release(x_43, 4);
 lean_ctor_release(x_43, 5);
 lean_ctor_release(x_43, 6);
 lean_ctor_release(x_43, 7);
 lean_ctor_release(x_43, 8);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_41, x_54);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_47);
lean_ctor_set(x_57, 4, x_48);
lean_ctor_set(x_57, 5, x_49);
lean_ctor_set(x_57, 6, x_50);
lean_ctor_set(x_57, 7, x_51);
lean_ctor_set(x_57, 8, x_52);
x_58 = lean_st_ref_set(x_1, x_57, x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = l_Lean_Name_num___override(x_40, x_41);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg(x_5, x_6);
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
x_14 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(x_4, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_expr_instantiate_rev(x_11, x_3);
lean_dec(x_11);
lean_inc(x_15);
x_18 = l_Lean_Expr_fvar___override(x_15);
x_19 = 0;
x_20 = l_Lean_LocalContext_mkLocalDecl(x_4, x_15, x_10, x_17, x_13, x_19);
lean_inc(x_18);
x_21 = lean_array_push(x_2, x_18);
x_22 = lean_array_push(x_3, x_18);
x_1 = x_12;
x_2 = x_21;
x_3 = x_22;
x_4 = x_20;
x_9 = x_16;
goto _start;
}
case 8:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(x_4, x_5, x_6, x_7, x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_expr_instantiate_rev(x_25, x_3);
lean_dec(x_25);
x_31 = 0;
lean_inc(x_28);
x_32 = l_Lean_Expr_fvar___override(x_28);
x_33 = 0;
x_34 = l_Lean_LocalContext_mkLocalDecl(x_4, x_28, x_24, x_30, x_31, x_33);
x_35 = lean_array_push(x_3, x_32);
x_1 = x_26;
x_3 = x_35;
x_4 = x_34;
x_9 = x_29;
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_InferType_inferType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1;
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_19 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = l_Lean_instInhabitedExpr;
x_28 = l_instInhabitedOfMonad___redArg(x_26, x_27);
x_29 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_panic_fn(x_30, x_1);
x_32 = lean_apply_6(x_31, x_2, x_3, x_4, x_5, x_6, x_7);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 2);
x_35 = lean_ctor_get(x_10, 3);
x_36 = lean_ctor_get(x_10, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_37 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_38 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_33);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_39, 0, x_33);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_40, 0, x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_42, 0, x_36);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_44, 0, x_34);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_8, 1, x_38);
lean_ctor_set(x_8, 0, x_45);
x_46 = l_ReaderT_instMonad___redArg(x_8);
x_47 = l_Lean_instInhabitedExpr;
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_6(x_51, x_2, x_3, x_4, x_5, x_6, x_7);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
lean_dec(x_8);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 x_58 = x_53;
} else {
 lean_dec_ref(x_53);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_60 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_54);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_61, 0, x_54);
x_62 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_62, 0, x_54);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_64, 0, x_57);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_65, 0, x_56);
x_66 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_66, 0, x_55);
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_66);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set(x_67, 4, x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
x_69 = l_ReaderT_instMonad___redArg(x_68);
x_70 = l_Lean_instInhabitedExpr;
x_71 = l_instInhabitedOfMonad___redArg(x_69, x_70);
x_72 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_73, 0, x_72);
x_74 = lean_panic_fn(x_73, x_1);
x_75 = lean_apply_6(x_74, x_2, x_3, x_4, x_5, x_6, x_7);
return x_75;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.InferType", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.InferType.inferType", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
x_2 = lean_unsigned_to_nat(73u);
x_3 = lean_unsigned_to_nat(129u);
x_4 = l_Lean_Compiler_LCNF_InferType_inferType___closed__1;
x_5 = l_Lean_Compiler_LCNF_InferType_inferType___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(x_14, x_15, x_3, x_5, x_6, x_7);
lean_dec(x_3);
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
x_20 = l_Lean_Compiler_LCNF_InferType_inferType___closed__3;
x_21 = l_panic___at___Lean_Compiler_LCNF_InferType_inferType_spec__0(x_20, x_2, x_3, x_4, x_5, x_6, x_7);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferLambdaType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0;
x_9 = l_Lean_Compiler_LCNF_InferType_inferLambdaType_go(x_1, x_8, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0;
x_9 = l_Lean_Compiler_LCNF_InferType_inferForallType_go(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_erasedExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Compiler_LCNF_InferType_inferType(x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_16, x_6, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_5, 0);
lean_dec(x_23);
x_24 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_30 = x_5;
} else {
 lean_dec_ref(x_5);
 x_30 = lean_box(0);
}
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_36 = lean_ctor_get(x_5, 1);
x_37 = lean_ctor_get(x_5, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
lean_dec(x_19);
x_39 = l_Lean_mkLevelIMax_x27(x_38, x_36);
lean_inc(x_1);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_1);
x_40 = 1;
x_41 = lean_usize_add(x_4, x_40);
x_4 = x_41;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; 
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_dec(x_5);
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
lean_dec(x_19);
x_45 = l_Lean_mkLevelIMax_x27(x_44, x_43);
lean_inc(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
x_47 = 1;
x_48 = lean_usize_add(x_4, x_47);
x_4 = x_48;
x_5 = x_46;
x_11 = x_34;
goto _start;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferForallType_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_13 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(x_3, x_4, x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_expr_instantiate_rev(x_10, x_2);
lean_dec(x_10);
lean_inc(x_14);
x_17 = l_Lean_Expr_fvar___override(x_14);
x_18 = 0;
x_19 = l_Lean_LocalContext_mkLocalDecl(x_3, x_14, x_9, x_16, x_12, x_18);
x_20 = lean_array_push(x_2, x_17);
x_1 = x_11;
x_2 = x_20;
x_3 = x_19;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Compiler_LCNF_InferType_getLevel_x3f(x_22, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_Lean_Compiler_LCNF_erasedExpr;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = l_Array_reverse___redArg(x_2);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_array_size(x_33);
x_37 = 0;
x_38 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0(x_34, x_33, x_36, x_37, x_35, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_Level_normalize(x_43);
lean_dec(x_43);
x_45 = l_Lean_Expr_sort___override(x_44);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = l_Lean_Level_normalize(x_47);
lean_dec(x_47);
x_49 = l_Lean_Expr_sort___override(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_39);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_38, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_53);
return x_38;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_ctor_get(x_40, 0);
lean_inc(x_55);
lean_dec(x_40);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
return x_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_23, 0);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_anyExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_14; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_5, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = l_Lean_Expr_headBeta(x_20);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_17, 0, x_23);
lean_inc(x_1);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_expr_instantiate_rev_range(x_22, x_21, x_5, x_2);
lean_dec(x_22);
x_25 = l_Lean_Expr_headBeta(x_24);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 0, x_26);
lean_inc(x_1);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_1);
x_27 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
lean_ctor_set(x_17, 0, x_25);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = l_Lean_Expr_headBeta(x_29);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_expr_instantiate_rev_range(x_31, x_30, x_5, x_2);
lean_dec(x_31);
x_35 = l_Lean_Expr_headBeta(x_34);
if (lean_obj_tag(x_35) == 7)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_1);
x_38 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Expr_headBeta(x_42);
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
x_9 = x_48;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_expr_instantiate_rev_range(x_45, x_43, x_5, x_2);
lean_dec(x_45);
x_50 = l_Lean_Expr_headBeta(x_49);
if (lean_obj_tag(x_50) == 7)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_5);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
lean_inc(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
x_9 = x_53;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_1);
x_54 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
}
}
}
block_13:
{
lean_object* x_11; 
x_11 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_11;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_getAppFn(x_1);
x_9 = l_Lean_Compiler_LCNF_InferType_inferType(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0;
x_14 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_14);
x_15 = lean_mk_array(x_14, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_15, x_17);
x_19 = lean_array_get_size(x_18);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
x_21 = lean_box(0);
lean_ctor_set(x_9, 1, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(x_21, x_18, x_20, x_22, x_12, x_11);
lean_dec(x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_expr_instantiate_rev_range(x_29, x_30, x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
lean_dec(x_30);
lean_dec(x_29);
x_32 = l_Lean_Expr_headBeta(x_31);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_expr_instantiate_rev_range(x_34, x_35, x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
lean_dec(x_35);
lean_dec(x_34);
x_37 = l_Lean_Expr_headBeta(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_18);
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_23, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
lean_ctor_set(x_23, 0, x_41);
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_45 = lean_ctor_get(x_9, 0);
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_9);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0;
x_49 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_49);
x_50 = lean_mk_array(x_49, x_48);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_49, x_51);
lean_dec(x_49);
x_53 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_50, x_52);
x_54 = lean_array_get_size(x_53);
lean_inc(x_54);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_47);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(x_56, x_53, x_55, x_58, x_47, x_46);
lean_dec(x_55);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_expr_instantiate_rev_range(x_65, x_66, x_54, x_53);
lean_dec(x_53);
lean_dec(x_54);
lean_dec(x_66);
lean_dec(x_65);
x_68 = l_Lean_Expr_headBeta(x_67);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_61);
lean_dec(x_54);
lean_dec(x_53);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_71 = x_59;
} else {
 lean_dec_ref(x_59);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
lean_dec(x_62);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
else
{
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkFreshFVarId___at___Lean_Compiler_LCNF_InferType_inferLambdaType_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_14; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_dec_lt(x_5, x_7);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = l_Lean_Expr_headBeta(x_20);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
lean_ctor_set(x_17, 0, x_23);
lean_inc(x_1);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
x_24 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_22, x_21, x_5, x_2);
lean_dec(x_22);
x_25 = l_Lean_Expr_headBeta(x_24);
if (lean_obj_tag(x_25) == 7)
{
lean_object* x_26; 
lean_dec(x_21);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_5);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 0, x_26);
lean_inc(x_1);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
lean_ctor_set(x_17, 0, x_25);
lean_ctor_set(x_4, 0, x_27);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = l_Lean_Expr_headBeta(x_29);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc(x_2);
x_34 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_31, x_30, x_5, x_2);
lean_dec(x_31);
x_35 = l_Lean_Expr_headBeta(x_34);
if (lean_obj_tag(x_35) == 7)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_5);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_37);
lean_ctor_set(x_4, 0, x_1);
x_9 = x_4;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Expr_headBeta(x_42);
if (lean_obj_tag(x_45) == 7)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
x_9 = x_48;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_inc(x_2);
x_49 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_45, x_43, x_5, x_2);
lean_dec(x_45);
x_50 = l_Lean_Expr_headBeta(x_49);
if (lean_obj_tag(x_50) == 7)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_5);
if (lean_is_scalar(x_44)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_44;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_5);
lean_inc(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
x_9 = x_53;
x_10 = x_6;
goto block_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_54 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0;
if (lean_is_scalar(x_44)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_44;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_43);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_6);
return x_57;
}
}
}
}
block_13:
{
lean_object* x_11; 
x_11 = lean_nat_add(x_5, x_8);
lean_dec(x_5);
x_4 = x_9;
x_5 = x_11;
x_6 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_2);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_2);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg(x_13, x_2, x_12, x_15, x_9, x_8);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_22, x_23, x_10, x_2);
lean_dec(x_10);
lean_dec(x_23);
lean_dec(x_22);
x_25 = l_Lean_Expr_headBeta(x_24);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_27, x_28, x_10, x_2);
lean_dec(x_10);
lean_dec(x_28);
lean_dec(x_27);
x_30 = l_Lean_Expr_headBeta(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_16, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_34);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppTypeCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_14;
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
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6;
x_2 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5;
x_3 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4;
x_4 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3;
x_5 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2;
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_ctor_get(x_3, 5);
x_8 = lean_st_ref_get(x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec(x_17);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7;
lean_inc(x_6);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_6);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 0, x_21);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_22);
lean_dec(x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7;
lean_inc(x_6);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_6);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_30);
lean_dec(x_30);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7;
lean_inc(x_6);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_6);
if (lean_is_scalar(x_31)) {
 x_35 = lean_alloc_ctor(3, 2, 0);
} else {
 x_35 = x_31;
 lean_ctor_set_tag(x_35, 3);
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_1);
lean_inc(x_7);
lean_ctor_set(x_8, 1, x_35);
lean_ctor_set(x_8, 0, x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_8);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_st_ref_get(x_2, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
 x_45 = lean_box(0);
}
x_46 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_44);
lean_dec(x_44);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7;
lean_inc(x_6);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_6);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(3, 2, 0);
} else {
 x_49 = x_45;
 lean_ctor_set_tag(x_49, 3);
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_1);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_42;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Environment_find_x3f(x_12, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_8);
x_15 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1;
x_16 = l_Lean_MessageData_ofConstName(x_1, x_13);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(x_19, x_4, x_5, x_6, x_11);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 0;
lean_inc(x_1);
x_26 = l_Lean_Environment_find_x3f(x_24, x_1, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1;
x_28 = l_Lean_MessageData_ofConstName(x_1, x_25);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(x_31, x_4, x_5, x_6, x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_19 = lean_nat_dec_lt(x_5, x_12);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
if (lean_obj_tag(x_22) == 7)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_hasLooseBVars(x_24);
if (x_25 == 0)
{
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_1);
x_14 = x_4;
x_15 = x_11;
goto block_18;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Compiler_LCNF_anyExpr;
x_27 = lean_expr_instantiate1(x_24, x_26);
lean_dec(x_24);
lean_inc(x_1);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_4, 0, x_1);
x_14 = x_4;
x_15 = x_11;
goto block_18;
}
}
else
{
uint8_t x_28; 
x_28 = l_Lean_Expr_isErased(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = lean_apply_8(x_2, lean_box(0), x_29, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_1);
lean_ctor_set(x_4, 0, x_1);
x_14 = x_4;
x_15 = x_31;
goto block_18;
}
else
{
uint8_t x_32; 
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
else
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_4, 1);
lean_inc(x_38);
lean_dec(x_4);
if (lean_obj_tag(x_38) == 7)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_hasLooseBVars(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_39);
x_14 = x_41;
x_15 = x_11;
goto block_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Compiler_LCNF_anyExpr;
x_43 = lean_expr_instantiate1(x_39, x_42);
lean_dec(x_39);
lean_inc(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
x_14 = x_44;
x_15 = x_11;
goto block_18;
}
}
else
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isErased(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
lean_inc(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_47 = lean_apply_8(x_2, lean_box(0), x_46, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_38);
x_14 = x_49;
x_15 = x_48;
goto block_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_38);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_11);
return x_56;
}
}
}
}
block_18:
{
lean_object* x_16; 
x_16 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_16;
x_11 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid projection", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1;
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_Expr_proj___override(x_2, x_3, x_13);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(x_18, x_8, x_9, x_10, x_11);
return x_19;
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
uint8_t x_16; 
x_16 = l_Lean_Expr_isAny(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___boxed), 11, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
x_18 = l_Lean_Expr_getAppFn(x_14);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = l_Lean_Environment_find_x3f(x_27, x_19, x_16);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_29, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 5)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
goto block_26;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1(x_37, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 6)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0;
x_46 = l_Lean_Expr_getAppNumArgs(x_14);
lean_inc(x_46);
x_47 = lean_mk_array(x_46, x_45);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_46, x_48);
lean_dec(x_46);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_14, x_47, x_49);
x_51 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
x_52 = lean_array_get_size(x_50);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_17);
goto block_43;
}
else
{
if (x_16 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_133; uint8_t x_134; 
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
lean_dec(x_44);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Expr_const___override(x_55, x_20);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_nat_dec_le(x_35, x_52);
if (x_134 == 0)
{
lean_dec(x_35);
x_58 = x_133;
x_59 = x_52;
goto block_132;
}
else
{
lean_dec(x_52);
x_58 = x_133;
x_59 = x_35;
goto block_132;
}
block_132:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Array_toSubarray___redArg(x_50, x_58, x_59);
x_61 = l_Array_ofSubarray___redArg(x_60);
x_62 = l_Lean_mkAppN(x_57, x_61);
lean_dec(x_61);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_63 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_62, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
x_67 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
if (lean_is_scalar(x_56)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_56;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_2);
lean_ctor_set(x_68, 2, x_48);
x_69 = lean_box(0);
lean_ctor_set(x_63, 1, x_65);
lean_ctor_set(x_63, 0, x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_70 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(x_69, x_17, x_68, x_63, x_67, x_4, x_5, x_6, x_7, x_8, x_66);
lean_dec(x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 7)
{
uint8_t x_74; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_70, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_ctor_set(x_70, 0, x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_70);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_70, 1);
x_82 = lean_ctor_get(x_70, 0);
lean_dec(x_82);
x_83 = l_Lean_Expr_isErased(x_73);
lean_dec(x_73);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_free_object(x_70);
x_84 = lean_box(0);
x_85 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_84, x_4, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_70, 0, x_86);
return x_70;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_70, 1);
lean_inc(x_87);
lean_dec(x_70);
x_88 = l_Lean_Expr_isErased(x_73);
lean_dec(x_73);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_box(0);
x_90 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_89, x_4, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = l_Lean_Compiler_LCNF_erasedExpr;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_71);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_70, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_72, 0);
lean_inc(x_95);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_95);
return x_70;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_70, 1);
lean_inc(x_96);
lean_dec(x_70);
x_97 = lean_ctor_get(x_72, 0);
lean_inc(x_97);
lean_dec(x_72);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_70);
if (x_99 == 0)
{
return x_70;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_70, 0);
x_101 = lean_ctor_get(x_70, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_70);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_63, 0);
x_104 = lean_ctor_get(x_63, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_63);
x_105 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
if (lean_is_scalar(x_56)) {
 x_106 = lean_alloc_ctor(0, 3, 0);
} else {
 x_106 = x_56;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_2);
lean_ctor_set(x_106, 2, x_48);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_103);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_109 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(x_107, x_17, x_106, x_108, x_105, x_4, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_106);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
if (lean_obj_tag(x_112) == 7)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
x_119 = l_Lean_Expr_isErased(x_112);
lean_dec(x_112);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
x_120 = lean_box(0);
x_121 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_120, x_4, x_5, x_6, x_7, x_8, x_117);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = l_Lean_Compiler_LCNF_erasedExpr;
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_117);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_110);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_126 = lean_ctor_get(x_111, 0);
lean_inc(x_126);
lean_dec(x_111);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_109, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_130 = x_109;
} else {
 lean_dec_ref(x_109);
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
}
else
{
lean_dec(x_56);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_17);
goto block_43;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
x_135 = lean_box(0);
x_136 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_135, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_136;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_box(0);
x_42 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8, x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
}
else
{
uint8_t x_137; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_38);
if (x_137 == 0)
{
return x_38;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_38, 0);
x_139 = lean_ctor_get(x_38, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_38);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
goto block_26;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
x_141 = lean_box(0);
x_142 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_141, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_142;
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_24, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_25;
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
x_143 = lean_box(0);
x_144 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_143, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_144;
}
}
else
{
lean_object* x_145; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = l_Lean_Compiler_LCNF_anyExpr;
lean_ctor_set(x_10, 0, x_145);
return x_10;
}
}
else
{
lean_object* x_146; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = l_Lean_Compiler_LCNF_erasedExpr;
lean_ctor_set(x_10, 0, x_146);
return x_10;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_10, 0);
x_148 = lean_ctor_get(x_10, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_10);
x_149 = l_Lean_Expr_headBeta(x_147);
x_150 = l_Lean_Expr_isErased(x_149);
if (x_150 == 0)
{
uint8_t x_151; 
x_151 = l_Lean_Expr_isAny(x_149);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_152 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___boxed), 11, 3);
lean_closure_set(x_152, 0, x_3);
lean_closure_set(x_152, 1, x_1);
lean_closure_set(x_152, 2, x_2);
x_153 = l_Lean_Expr_getAppFn(x_149);
if (lean_obj_tag(x_153) == 4)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_162; lean_object* x_163; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_st_ref_get(x_8, x_148);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_162 = lean_ctor_get(x_157, 0);
lean_inc(x_162);
lean_dec(x_157);
x_163 = l_Lean_Environment_find_x3f(x_162, x_154, x_151);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
x_164 = lean_box(0);
x_165 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_164, x_4, x_5, x_6, x_7, x_8, x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_165;
}
else
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_163, 0);
lean_inc(x_166);
lean_dec(x_163);
if (lean_obj_tag(x_166) == 5)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_ctor_get(x_167, 4);
lean_inc(x_168);
if (lean_obj_tag(x_168) == 0)
{
lean_dec(x_167);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
goto block_161;
}
else
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_167, 2);
lean_inc(x_171);
lean_dec(x_167);
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
lean_dec(x_168);
x_173 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1(x_172, x_4, x_5, x_6, x_7, x_8, x_158);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
if (lean_obj_tag(x_174) == 6)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_174, 0);
lean_inc(x_179);
lean_dec(x_174);
x_180 = l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0;
x_181 = l_Lean_Expr_getAppNumArgs(x_149);
lean_inc(x_181);
x_182 = lean_mk_array(x_181, x_180);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_sub(x_181, x_183);
lean_dec(x_181);
x_185 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_149, x_182, x_184);
x_186 = lean_nat_add(x_170, x_171);
lean_dec(x_171);
x_187 = lean_array_get_size(x_185);
x_188 = lean_nat_dec_eq(x_186, x_187);
lean_dec(x_186);
if (x_188 == 0)
{
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_179);
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_152);
goto block_178;
}
else
{
if (x_151 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_230; uint8_t x_231; 
x_189 = lean_ctor_get(x_179, 0);
lean_inc(x_189);
lean_dec(x_179);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Expr_const___override(x_190, x_155);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_le(x_170, x_187);
if (x_231 == 0)
{
lean_dec(x_170);
x_193 = x_230;
x_194 = x_187;
goto block_229;
}
else
{
lean_dec(x_187);
x_193 = x_230;
x_194 = x_170;
goto block_229;
}
block_229:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = l_Array_toSubarray___redArg(x_185, x_193, x_194);
x_196 = l_Array_ofSubarray___redArg(x_195);
x_197 = l_Lean_mkAppN(x_192, x_196);
lean_dec(x_196);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_198 = l_Lean_Compiler_LCNF_InferType_inferAppType(x_197, x_4, x_5, x_6, x_7, x_8, x_175);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
if (lean_is_scalar(x_191)) {
 x_203 = lean_alloc_ctor(0, 3, 0);
} else {
 x_203 = x_191;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 2, x_183);
x_204 = lean_box(0);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_199);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_206 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(x_204, x_152, x_203, x_205, x_202, x_4, x_5, x_6, x_7, x_8, x_200);
lean_dec(x_203);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
if (lean_obj_tag(x_209) == 7)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec(x_209);
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
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_206, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_215 = x_206;
} else {
 lean_dec_ref(x_206);
 x_215 = lean_box(0);
}
x_216 = l_Lean_Expr_isErased(x_209);
lean_dec(x_209);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_215);
x_217 = lean_box(0);
x_218 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_217, x_4, x_5, x_6, x_7, x_8, x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_219 = l_Lean_Compiler_LCNF_erasedExpr;
if (lean_is_scalar(x_215)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_215;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_214);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_207);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_206, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_222 = x_206;
} else {
 lean_dec_ref(x_206);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_208, 0);
lean_inc(x_223);
lean_dec(x_208);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_ctor_get(x_206, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_206, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_227 = x_206;
} else {
 lean_dec_ref(x_206);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_dec(x_191);
lean_dec(x_152);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_198;
}
}
}
else
{
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_179);
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_152);
goto block_178;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
x_232 = lean_box(0);
x_233 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_232, x_4, x_5, x_6, x_7, x_8, x_175);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_233;
}
block_178:
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_box(0);
x_177 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_176, x_4, x_5, x_6, x_7, x_8, x_175);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_177;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_173, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_173, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_236 = x_173;
} else {
 lean_dec_ref(x_173);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
goto block_161;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_166);
lean_dec(x_155);
lean_dec(x_152);
lean_dec(x_149);
x_238 = lean_box(0);
x_239 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_238, x_4, x_5, x_6, x_7, x_8, x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_239;
}
}
block_161:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_box(0);
x_160 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_159, x_4, x_5, x_6, x_7, x_8, x_158);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_160;
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_149);
x_240 = lean_box(0);
x_241 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_3, x_1, x_2, lean_box(0), x_240, x_4, x_5, x_6, x_7, x_8, x_148);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_149);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = l_Lean_Compiler_LCNF_anyExpr;
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_148);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_149);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_244 = l_Lean_Compiler_LCNF_erasedExpr;
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_148);
return x_245;
}
}
}
else
{
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
x_20 = l_Lean_Compiler_LCNF_InferType_inferConstType___redArg(x_17, x_18, x_3, x_5, x_6, x_7);
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
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_20;
}
}
default: 
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_2);
x_26 = l_Lean_Compiler_LCNF_InferType_getType(x_24, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_27, x_25, x_2, x_3, x_4, x_5, x_6, x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_29;
}
else
{
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
x_8 = l_Lean_Compiler_LCNF_InferType_inferType(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
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
static lean_object* _init_l_Lean_Compiler_LCNF_getLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_getLevel___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_getLevel___closed__0;
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
x_19 = l_Lean_Compiler_LCNF_getLevel___closed__1;
x_20 = l_Lean_indentExpr(x_1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_23, x_3, x_4, x_5, x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_28 = l_Lean_Compiler_LCNF_getLevel___closed__1;
x_29 = l_Lean_indentExpr(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_32, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
x_8 = l_Lean_Compiler_LCNF_InferType_inferArgType(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
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
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
x_13 = l_Lean_Compiler_LCNF_InferType_inferAppTypeCore(x_10, x_8, x_12, x_2, x_3, x_4, x_5, x_11);
return x_13;
}
else
{
lean_dec(x_8);
return x_9;
}
}
case 4:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
case 5:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_getType(x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
default: 
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_1 = x_21;
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
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_InferType_mkForallParams_spec__0(x_11, x_12, x_1);
x_14 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5;
x_15 = l_Lean_Compiler_LCNF_InferType_mkForallFVars(x_13, x_9, x_14, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_9);
lean_dec(x_13);
return x_15;
}
else
{
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Compiler_LCNF_Code_inferType(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_Code_inferType(x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_inferType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Alt_inferType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_2, x_4, x_7);
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
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
x_12 = l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg(x_1, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_3, x_5, x_14);
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
static lean_object* _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0;
x_10 = lean_array_push(x_9, x_1);
x_11 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
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
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = lean_apply_1(x_1, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_Alt_inferType(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_joinTypes(x_3, x_13);
x_2 = x_10;
x_3 = x_15;
x_8 = x_14;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
case 1:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(x_1, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_fget(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLt___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_PRange_instSupportsUpperBoundOpenOfDecidableLT___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PRange_instUpwardEnumerableNat;
x_2 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__1;
x_3 = lean_alloc_closure((void*)(l_Std_PRange_instIteratorRangeIteratorIdOfUpwardEnumerableOfSupportsUpperBound___redArg___lam__0), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__4;
x_2 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__8;
x_2 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__7;
x_3 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__6;
x_4 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__5;
x_5 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__9;
x_2 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__2;
x_2 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__12;
x_3 = l_Std_Iterators_Types_Attach_instIterator___redArg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`Code.bind` failed, empty `cases` found", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkCasesResultType___lam__0___boxed), 2, 0);
x_8 = l_Lean_Compiler_LCNF_instInhabitedAlt;
x_9 = l_Array_isEmpty___redArg(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_8, x_1, x_10);
x_12 = l_Lean_Compiler_LCNF_Alt_inferType(x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_array_get_size(x_1);
x_18 = l_Array_toSubarray___redArg(x_1, x_16, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkCasesResultType___lam__2___boxed), 2, 1);
lean_closure_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_12, 1, x_20);
lean_ctor_set(x_12, 0, x_22);
x_23 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__12;
x_24 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__13;
lean_inc(x_7);
x_25 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_7, x_24, x_23);
x_26 = l_Std_Iterators_instIteratorMap___redArg(x_23, x_25, x_7, x_21);
x_27 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(x_26, x_12, x_14, x_2, x_3, x_4, x_5, x_15);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_array_get_size(x_1);
x_32 = l_Array_toSubarray___redArg(x_1, x_30, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 2);
lean_inc(x_34);
x_35 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkCasesResultType___lam__2___boxed), 2, 1);
lean_closure_set(x_35, 0, x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__12;
x_39 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__13;
lean_inc(x_7);
x_40 = l_Std_Iterators_Types_ULiftIterator_instIterator___redArg(x_7, x_39, x_38);
x_41 = l_Std_Iterators_instIteratorMap___redArg(x_38, x_40, x_7, x_35);
x_42 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(x_41, x_37, x_28, x_2, x_3, x_4, x_5, x_29);
return x_42;
}
}
else
{
lean_dec(x_7);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_1);
x_43 = l_Lean_Compiler_LCNF_mkCasesResultType___closed__15;
x_44 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1___redArg(x_43, x_3, x_4, x_5, x_6);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Iterators_IterM_DefaultConsumers_forIn_x27___at___Lean_Compiler_LCNF_mkCasesResultType_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_mkCasesResultType___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkCasesResultType___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_mkCasesResultType___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1;
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_16 = lean_ctor_get(x_9, 1);
lean_dec(x_16);
x_17 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_18 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_19, 0, x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_24, 0, x_13);
lean_ctor_set(x_9, 4, x_22);
lean_ctor_set(x_9, 3, x_23);
lean_ctor_set(x_9, 2, x_24);
lean_ctor_set(x_9, 1, x_17);
lean_ctor_set(x_9, 0, x_21);
lean_ctor_set(x_7, 1, x_18);
x_25 = l_ReaderT_instMonad___redArg(x_7);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = l_instInhabitedOfMonad___redArg(x_25, x_27);
x_29 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_panic_fn(x_29, x_1);
x_31 = lean_apply_5(x_30, x_2, x_3, x_4, x_5, x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 2);
x_34 = lean_ctor_get(x_9, 3);
x_35 = lean_ctor_get(x_9, 4);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_36 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_37 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_32);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_35);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_33);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_44);
x_45 = l_ReaderT_instMonad___redArg(x_7);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = l_instInhabitedOfMonad___redArg(x_45, x_47);
x_49 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_panic_fn(x_49, x_1);
x_51 = lean_apply_5(x_50, x_2, x_3, x_4, x_5, x_6);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_52 = lean_ctor_get(x_7, 0);
lean_inc(x_52);
lean_dec(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 3);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 4);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
x_58 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2;
x_59 = l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3;
lean_inc(x_53);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_60, 0, x_53);
x_61 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_61, 0, x_53);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_63, 0, x_56);
x_64 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_64, 0, x_55);
x_65 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_65, 0, x_54);
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(0, 5, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_64);
lean_ctor_set(x_66, 4, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_59);
x_68 = l_ReaderT_instMonad___redArg(x_67);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = l_instInhabitedOfMonad___redArg(x_68, x_70);
x_72 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_72, 0, x_71);
x_73 = lean_panic_fn(x_72, x_1);
x_74 = lean_apply_5(x_73, x_2, x_3, x_4, x_5, x_6);
return x_74;
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.LCNF.isErasedCompatible.go", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_InferType_inferType___closed__2;
x_2 = lean_unsigned_to_nat(50u);
x_3 = lean_unsigned_to_nat(320u);
x_4 = l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0;
x_5 = l_Lean_Compiler_LCNF_InferType_inferType___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_20 = l_Lean_Expr_headBeta(x_1);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_array_get_size(x_2);
x_24 = lean_nat_sub(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = lean_box(x_22);
x_28 = lean_array_get(x_27, x_2, x_26);
lean_dec(x_26);
lean_dec(x_2);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
case 1:
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = l_Lean_Compiler_LCNF_getType(x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lean_Compiler_LCNF_isPredicateType(x_35);
x_37 = lean_box(x_36);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = l_Lean_Compiler_LCNF_isPredicateType(x_38);
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 3:
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
case 4:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = l_Lean_Expr_isErased(x_20);
lean_dec(x_20);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
case 5:
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_20, 0);
lean_inc(x_53);
lean_dec(x_20);
x_1 = x_53;
goto _start;
}
case 6:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_20, 2);
lean_inc(x_56);
lean_dec(x_20);
x_8 = x_55;
x_9 = x_56;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
goto block_19;
}
case 7:
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_20, 2);
lean_inc(x_58);
lean_dec(x_20);
x_8 = x_57;
x_9 = x_58;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
goto block_19;
}
case 10:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_dec(x_20);
x_1 = x_59;
goto _start;
}
default: 
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_20);
lean_dec(x_2);
x_61 = l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1;
x_62 = l_panic___at___Lean_Compiler_LCNF_isErasedCompatible_go_spec__0(x_61, x_3, x_4, x_5, x_6, x_7);
return x_62;
}
}
block_19:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Compiler_LCNF_isPredicateType(x_8);
x_16 = lean_box(x_15);
x_17 = lean_array_push(x_2, x_16);
x_1 = x_9;
x_2 = x_17;
x_3 = x_10;
x_4 = x_11;
x_5 = x_12;
x_6 = x_13;
x_7 = x_14;
goto _start;
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
LEAN_EXPORT uint8_t l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(lean_object* x_1, lean_object* x_2) {
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
return x_10;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_expr_eqv(x_1, x_2);
x_11 = 1;
if (x_10 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Expr_isErased(x_1);
if (x_57 == 0)
{
x_12 = x_57;
goto block_56;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_Expr_isErased(x_2);
x_12 = x_58;
goto block_56;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
block_9:
{
uint8_t x_7; 
x_7 = l_Lean_Compiler_LCNF_eqvTypes(x_3, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
block_56:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_Expr_headBeta(x_1);
lean_inc(x_2);
x_14 = l_Lean_Expr_headBeta(x_2);
x_15 = lean_expr_eqv(x_1, x_13);
if (x_15 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = lean_expr_eqv(x_2, x_14);
if (x_17 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
switch (lean_obj_tag(x_1)) {
case 3:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_Level_isEquiv(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
return x_21;
}
case 10:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_2 = x_22;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 4:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_name_eq(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
return x_29;
}
}
case 10:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_2 = x_30;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Compiler_LCNF_eqvTypes(x_32, x_34);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
return x_36;
}
else
{
x_1 = x_33;
x_2 = x_35;
goto _start;
}
}
case 10:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
lean_dec(x_2);
x_2 = x_38;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
case 6:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_3 = x_40;
x_4 = x_41;
x_5 = x_42;
x_6 = x_43;
goto block_9;
}
case 10:
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_2 = x_44;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
case 7:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 2);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_dec(x_2);
x_3 = x_46;
x_4 = x_47;
x_5 = x_48;
x_6 = x_49;
goto block_9;
}
case 10:
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_2, 1);
lean_inc(x_50);
lean_dec(x_2);
x_2 = x_50;
goto _start;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
case 10:
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_1 = x_52;
goto _start;
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
lean_dec(x_2);
x_2 = x_54;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_isEqv___at___Lean_Compiler_LCNF_eqvTypes_spec__0(x_1, x_2);
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
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__0);
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__1);
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__2);
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__3);
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__4);
l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_mkForallParams___redArg___closed__5);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__0);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__1);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__2);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__3);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__4);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__5);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__6);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__7);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__8);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__9);
l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10 = _init_l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_withLocalDecl___redArg___closed__10);
l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__0);
l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferConstType___redArg___closed__1);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__0);
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
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__7);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__8);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__9);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__10);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__11);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__12);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__13);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__14);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__15);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__16);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__17);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__18);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__19);
l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20 = _init_l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLitValueType___closed__20);
l_Lean_Compiler_LCNF_InferType_inferType___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__0);
l_Lean_Compiler_LCNF_InferType_inferType___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__1);
l_Lean_Compiler_LCNF_InferType_inferType___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__2);
l_Lean_Compiler_LCNF_InferType_inferType___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferType___closed__3);
l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferLambdaType___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_InferType_inferForallType_go_spec__0___closed__0);
l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0 = _init_l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_InferType_inferAppType_spec__0___redArg___closed__0);
l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferAppType___closed__0);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__0);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__1);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__2);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__3);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__4);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__5);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__6);
l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7 = _init_l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7();
lean_mark_persistent(l_Lean_throwError___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__0___redArg___closed__7);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__0);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__1);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__2);
l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3 = _init_l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___Lean_Compiler_LCNF_InferType_inferProjType_spec__1___closed__3);
l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0 = _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__0);
l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1 = _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__1);
l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2 = _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__2);
l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3 = _init_l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_InferType_inferProjType___lam__0___closed__3);
l_Lean_Compiler_LCNF_getLevel___closed__0 = _init_l_Lean_Compiler_LCNF_getLevel___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_getLevel___closed__0);
l_Lean_Compiler_LCNF_getLevel___closed__1 = _init_l_Lean_Compiler_LCNF_getLevel___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_getLevel___closed__1);
l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0 = _init_l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkAuxJpDecl_x27___closed__0);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__0 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__0);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__1 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__1);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__2 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__2);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__3 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__3);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__4 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__4);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__5 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__5);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__6 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__6);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__7 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__7);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__8 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__8);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__9 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__9);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__10 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__10);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__11 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__11);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__12 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__12);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__13 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__13);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__14 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__14);
l_Lean_Compiler_LCNF_mkCasesResultType___closed__15 = _init_l_Lean_Compiler_LCNF_mkCasesResultType___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_mkCasesResultType___closed__15);
l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0 = _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__0);
l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1 = _init_l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_isErasedCompatible_go___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
