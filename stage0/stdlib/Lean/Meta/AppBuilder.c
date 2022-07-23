// Lean compiler output
// Module: Lean.Meta.AppBuilder
// Imports: Init Lean.Structure Lean.Util.Recognizers Lean.Meta.SynthInstance Lean.Meta.Check Lean.Meta.DecLevel
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__6;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_mkLt___closed__4;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongr___closed__1;
static lean_object* l_Lean_Meta_mkListLit___closed__6;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqMP___closed__3;
static lean_object* l_Lean_Meta_mkOfNonempty___closed__4;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__1;
static lean_object* l_Lean_Meta_mkEqSymm___closed__1;
static lean_object* l_Lean_Meta_mkLe___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_mkDecideProof___closed__1;
static lean_object* l_Lean_Meta_mkAbsurd___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkImpCongr___closed__2;
static lean_object* l_Lean_Meta_mkAbsurd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3;
static lean_object* l_Lean_Meta_mkDecideProof___closed__2;
static lean_object* l_Lean_Meta_mkPure___closed__2;
static lean_object* l_Lean_Meta_mkAdd___closed__1;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__4;
static lean_object* l_Lean_Meta_mkCongr___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkPure___closed__4;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__4;
static lean_object* l_Lean_Meta_mkPure___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5;
static lean_object* l_Lean_Meta_mkDefault___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkFalseElim___closed__3;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkId___closed__2;
static lean_object* l_Lean_Meta_mkDefault___closed__2;
static lean_object* l_Lean_Meta_mkMul___closed__4;
static lean_object* l_Lean_Meta_mkDecide___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3;
static lean_object* l_Lean_Meta_mkFunExt___closed__1;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecide___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_mkAppM_x27___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__5;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
static lean_object* l_Lean_Meta_mkId___closed__1;
static lean_object* l_Lean_Meta_mkSorry___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__9;
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLetBodyCongr___closed__2;
static lean_object* l_Lean_Meta_mkDecide___closed__1;
static lean_object* l_Lean_Meta_mkProjection___closed__4;
static lean_object* l_Lean_Meta_mkSorry___closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_mkLetBodyCongr___closed__1;
static lean_object* l_Lean_Meta_mkCongrArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHEqSymm___closed__3;
static lean_object* l_Lean_Meta_mkNumeral___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqNDRec___closed__3;
static lean_object* l_Lean_Meta_mkEqTrue___closed__2;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__4;
static lean_object* l_Lean_Meta_mkFalseElim___closed__1;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__7;
static lean_object* l_Lean_Meta_mkOfNonempty___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__3;
static lean_object* l_Lean_Meta_mkPure___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6;
lean_object* l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__2;
static lean_object* l_Lean_Meta_mkHEq___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkFalseElim___closed__4;
static lean_object* l_Lean_Meta_mkDefault___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAppM_x27___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkDecide___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1(lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqSymm___closed__2;
static lean_object* l_Lean_Meta_mkSub___closed__1;
static lean_object* l_Lean_Meta_mkEqFalse___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqMP___closed__1;
static lean_object* l_Lean_Meta_mkOfNonempty___closed__1;
static lean_object* l_Lean_Meta_mkEqMP___closed__2;
static lean_object* l_Lean_Meta_mkNumeral___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__5;
lean_object* l_Lean_mkRawNatLit(lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__3;
static lean_object* l_Lean_Meta_mkImpCongrCtx___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__3;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__5;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqNDRec___closed__6;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__2;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__1;
static lean_object* l_Lean_Meta_mkLetValCongr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNumeral___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLetValCongr___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__4;
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__2;
static lean_object* l_Lean_Meta_mkEqRec___closed__2;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecideProof___closed__4;
static lean_object* l_Lean_Meta_mkListLit___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4;
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_mkNumeral___closed__1;
static lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqTrans___closed__1;
static lean_object* l_Lean_Meta_mkDefault___closed__3;
static lean_object* l_Lean_Meta_mkLetCongr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqRec___closed__1;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkLetCongr___closed__2;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__3;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_mkFalseElim___closed__2;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkListLit___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLe___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqSymm___closed__5;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__5;
static lean_object* l_Lean_Meta_mkForallCongr___closed__2;
static lean_object* l_Lean_Meta_mkEqTrans___closed__2;
static lean_object* l_Lean_Meta_mkAppM___closed__2;
static lean_object* l_Lean_Meta_mkEqFalse_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkForallCongr___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkPropExt___closed__1;
static lean_object* l_Lean_Meta_mkCongrFun___closed__1;
static lean_object* l_Lean_Meta_mkArrayLit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__1;
static lean_object* l_Lean_Meta_mkMul___closed__2;
static lean_object* l_Lean_Meta_mkCongrFun___closed__2;
static lean_object* l_Lean_Meta_mkEqMPR___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__3;
static lean_object* l_Lean_Meta_mkEqSymm___closed__3;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7;
static lean_object* l_Lean_Meta_mkPropExt___closed__2;
static lean_object* l_Lean_Meta_mkImpCongrCtx___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqNDRec___closed__4;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_mkEqRefl___closed__1;
static lean_object* l_Lean_Meta_mkEqFalse_x27___closed__1;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1;
static lean_object* l_Lean_Meta_mkOfEqTrue___closed__1;
static lean_object* l_Lean_Meta_mkArrayLit___closed__1;
static lean_object* l_Lean_Meta_mkOfNonempty___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrFun___closed__4;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__2;
static lean_object* l_Lean_Meta_mkFunExt___closed__2;
static lean_object* l_Lean_Meta_mkSorry___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3;
static lean_object* l_Lean_Meta_mkEqRefl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__5;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__5;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__4;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkListLit___closed__3;
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkListLit___closed__5;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__2;
static lean_object* l_Lean_Meta_mkEqTrue___closed__1;
static lean_object* l_Lean_Meta_mkEqSymm___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__6;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isMonad_x3f___closed__1;
static lean_object* l_Lean_Meta_mkAppM___closed__1;
static lean_object* l_Lean_Meta_mkMul___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSyntheticSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__3;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__9;
static lean_object* l_Lean_Meta_mkEqMPR___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_5792_(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__3;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__1;
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecideProof___closed__3;
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isMonad_x3f___closed__2;
static lean_object* l_Lean_Meta_mkAppM___lambda__1___closed__6;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__4;
static lean_object* l_Lean_Meta_mkEq___closed__2;
static lean_object* l_Lean_Meta_mkSorry___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__4;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__10;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4;
static lean_object* l_Lean_Meta_mkAppM___closed__3;
lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEq___closed__1;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__5;
static lean_object* l_Lean_Meta_mkSorry___closed__5;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__4;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAppM___closed__4;
static lean_object* l_Lean_Meta_mkLt___closed__3;
static lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkHEqTrans___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkMul___closed__3;
static lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_mkLe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkImpCongr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrFun___closed__5;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__7;
static lean_object* l_Lean_Meta_mkSorry___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkOfEqTrue___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7;
static lean_object* l_Lean_Meta_mkListLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrFun___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4;
static lean_object* _init_l_Lean_Meta_mkId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkId___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_mkId___closed__2;
x_16 = l_Lean_Expr_const___override(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_mkId___closed__2;
x_23 = l_Lean_Expr_const___override(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_Meta_getLevel(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkId___closed__2;
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_mkAppB(x_14, x_2, x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_mkId___closed__2;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_mkAppB(x_21, x_2, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Lean_Meta_mkEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_mkEq___closed__2;
x_17 = l_Lean_Expr_const___override(x_16, x_15);
x_18 = l_Lean_mkApp3(x_17, x_9, x_1, x_2);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_mkEq___closed__2;
x_24 = l_Lean_Expr_const___override(x_23, x_22);
x_25 = l_Lean_mkApp3(x_24, x_9, x_1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkHEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HEq", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkHEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkHEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
x_14 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkHEq___closed__2;
x_20 = l_Lean_Expr_const___override(x_19, x_18);
x_21 = l_Lean_mkApp4(x_20, x_9, x_1, x_12, x_2);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Meta_mkHEq___closed__2;
x_27 = l_Lean_Expr_const___override(x_26, x_25);
x_28 = l_Lean_mkApp4(x_27, x_9, x_1, x_12, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_23);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
return x_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_11, 0);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_11);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
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
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
x_14 = l_Lean_Meta_getLevel(x_9, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_9);
x_17 = l_Lean_Meta_isExprDefEq(x_9, x_12, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_mkHEq___closed__2;
x_25 = l_Lean_Expr_const___override(x_24, x_23);
x_26 = l_Lean_mkApp4(x_25, x_9, x_1, x_12, x_2);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_mkHEq___closed__2;
x_31 = l_Lean_Expr_const___override(x_30, x_29);
x_32 = l_Lean_mkApp4(x_31, x_9, x_1, x_12, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_12);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_17, 0);
lean_dec(x_35);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_15);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_mkEq___closed__2;
x_39 = l_Lean_Expr_const___override(x_38, x_37);
x_40 = l_Lean_mkApp3(x_39, x_9, x_1, x_2);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_15);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_mkEq___closed__2;
x_45 = l_Lean_Expr_const___override(x_44, x_43);
x_46 = l_Lean_mkApp3(x_45, x_9, x_1, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_17);
if (x_48 == 0)
{
return x_17;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_17, 0);
x_50 = lean_ctor_get(x_17, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_17);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
return x_11;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_11, 0);
x_58 = lean_ctor_get(x_11, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_11);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_8);
if (x_60 == 0)
{
return x_8;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_8, 0);
x_62 = lean_ctor_get(x_8, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_8);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("refl", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_mkEqRefl___closed__2;
x_16 = l_Lean_Expr_const___override(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_mkEqRefl___closed__2;
x_23 = l_Lean_Expr_const___override(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkHEqRefl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkHEq___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_Lean_Meta_getLevel(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_mkHEqRefl___closed__1;
x_16 = l_Lean_Expr_const___override(x_15, x_14);
x_17 = l_Lean_mkAppB(x_16, x_8, x_1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Meta_mkHEqRefl___closed__1;
x_23 = l_Lean_Expr_const___override(x_22, x_21);
x_24 = l_Lean_mkAppB(x_23, x_8, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
return x_7;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAbsurd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("absurd", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAbsurd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkAbsurd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_9 = lean_infer_type(x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Meta_getLevel(x_1, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_mkAbsurd___closed__2;
x_18 = l_Lean_Expr_const___override(x_17, x_16);
x_19 = l_Lean_mkApp4(x_18, x_10, x_1, x_2, x_3);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_mkAbsurd___closed__2;
x_25 = l_Lean_Expr_const___override(x_24, x_23);
x_26 = l_Lean_mkApp4(x_25, x_10, x_1, x_2, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkFalseElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkFalseElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkFalseElim___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkFalseElim___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elim", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkFalseElim___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkFalseElim___closed__2;
x_2 = l_Lean_Meta_mkFalseElim___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkFalseElim___closed__4;
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_mkAppB(x_14, x_1, x_2);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_mkFalseElim___closed__4;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_mkAppB(x_21, x_1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_whnfD(x_8, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nhas type", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_indentExpr(x_1);
x_4 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_5 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_indentExpr(x_2);
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("AppBuilder for '", 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', ", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_2);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg(x_15, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("symm", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality proof expected", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqSymm___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqSymm___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_mkEqRefl___closed__2;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkEq___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_10);
x_16 = l_Lean_Meta_mkEqSymm___closed__5;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_mkEqSymm___closed__2;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Expr_appFn_x21(x_10);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_24 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_22);
x_25 = l_Lean_Meta_getLevel(x_22, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Meta_mkEqSymm___closed__2;
x_31 = l_Lean_Expr_const___override(x_30, x_29);
x_32 = l_Lean_mkApp4(x_31, x_22, x_23, x_24, x_1);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_mkEqSymm___closed__2;
x_38 = l_Lean_Expr_const___override(x_37, x_36);
x_39 = l_Lean_mkApp4(x_38, x_22, x_23, x_24, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
return x_9;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_9);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_6);
return x_49;
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrans___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("trans", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrans___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkEqRefl___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_52 = l_Lean_Meta_mkEq___closed__2;
x_53 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Expr_isAppOfArity(x_15, x_52, x_53);
x_55 = l_Lean_Expr_isAppOfArity(x_12, x_52, x_53);
if (x_54 == 0)
{
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_15);
lean_dec(x_2);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_57 = l_Lean_Meta_mkEqSymm___closed__5;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_mkEqTrans___closed__2;
x_60 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_59, x_58, x_3, x_4, x_5, x_6, x_16);
return x_60;
}
else
{
lean_object* x_61; 
x_61 = lean_box(0);
x_17 = x_61;
goto block_51;
}
}
else
{
if (x_55 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_15);
lean_dec(x_2);
x_62 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_63 = l_Lean_Meta_mkEqSymm___closed__5;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Meta_mkEqTrans___closed__2;
x_66 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_65, x_64, x_3, x_4, x_5, x_6, x_16);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_67 = l_Lean_Expr_appFn_x21(x_15);
x_68 = l_Lean_Expr_appFn_x21(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_68);
lean_dec(x_68);
x_70 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_71 = l_Lean_Expr_appArg_x21(x_15);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_17 = x_74;
goto block_51;
}
}
block_51:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_19 = l_Lean_Meta_mkEqSymm___closed__5;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_mkEqTrans___closed__2;
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_21, x_20, x_3, x_4, x_5, x_6, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_Expr_appFn_x21(x_12);
x_25 = l_Lean_Expr_appFn_x21(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_28 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_26);
x_31 = l_Lean_Meta_getLevel(x_26, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_mkEqTrans___closed__2;
x_37 = l_Lean_Expr_const___override(x_36, x_35);
x_38 = l_Lean_mkApp6(x_37, x_26, x_27, x_28, x_30, x_1, x_2);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_mkEqTrans___closed__2;
x_44 = l_Lean_Expr_const___override(x_43, x_42);
x_45 = l_Lean_mkApp6(x_44, x_26, x_27, x_28, x_30, x_1, x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
return x_14;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_14, 0);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_11);
if (x_79 == 0)
{
return x_11;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_11, 0);
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_11);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_7);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_7);
return x_84;
}
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkHEq___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("heterogeneous equality proof expected", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHEqSymm___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHEqSymm___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_mkHEqRefl___closed__1;
x_8 = l_Lean_Expr_isAppOf(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkHEq___closed__2;
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_10);
x_16 = l_Lean_Meta_mkHEqSymm___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_mkHEqSymm___closed__1;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Expr_appFn_x21(x_10);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_26 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_23);
x_27 = l_Lean_Meta_getLevel(x_23, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_mkHEqSymm___closed__1;
x_33 = l_Lean_Expr_const___override(x_32, x_31);
x_34 = l_Lean_mkApp5(x_33, x_23, x_25, x_24, x_26, x_1);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_mkHEqSymm___closed__1;
x_40 = l_Lean_Expr_const___override(x_39, x_38);
x_41 = l_Lean_mkApp5(x_40, x_23, x_25, x_24, x_26, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
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
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
return x_9;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_9);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_6);
return x_51;
}
}
}
static lean_object* _init_l_Lean_Meta_mkHEqTrans___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkHEq___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkHEqRefl___closed__1;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkHEq___closed__2;
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
x_20 = l_Lean_Expr_isAppOfArity(x_12, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_21 = x_65;
goto block_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = l_Lean_Expr_appFn_x21(x_15);
x_67 = l_Lean_Expr_appFn_x21(x_66);
x_68 = l_Lean_Expr_appFn_x21(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_68);
lean_dec(x_68);
x_70 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_71 = l_Lean_Expr_appArg_x21(x_66);
lean_dec(x_66);
x_72 = l_Lean_Expr_appArg_x21(x_15);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_21 = x_76;
goto block_64;
}
block_64:
{
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_23 = l_Lean_Meta_mkHEqSymm___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_mkHEqTrans___closed__1;
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_25, x_24, x_3, x_4, x_5, x_6, x_16);
return x_26;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_1);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_28 = l_Lean_Meta_mkHEqSymm___closed__4;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_mkHEqTrans___closed__1;
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_30, x_29, x_3, x_4, x_5, x_6, x_16);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_15);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Expr_appFn_x21(x_12);
x_34 = l_Lean_Expr_appFn_x21(x_33);
x_35 = l_Lean_Expr_appFn_x21(x_34);
x_36 = l_Lean_Expr_appArg_x21(x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_38 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_39 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_36);
x_44 = l_Lean_Meta_getLevel(x_36, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_mkHEqTrans___closed__1;
x_50 = l_Lean_Expr_const___override(x_49, x_48);
x_51 = l_Lean_mkApp8(x_50, x_36, x_38, x_42, x_37, x_39, x_43, x_1, x_2);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_mkHEqTrans___closed__1;
x_57 = l_Lean_Expr_const___override(x_56, x_55);
x_58 = l_Lean_mkApp8(x_57, x_36, x_38, x_42, x_37, x_39, x_43, x_1, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_14);
if (x_77 == 0)
{
return x_14;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_14, 0);
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_11);
if (x_81 == 0)
{
return x_11;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_11, 0);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_11);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_7);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_2);
lean_ctor_set(x_86, 1, x_7);
return x_86;
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_of_heq", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_getLevel(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2;
x_17 = l_Lean_Expr_const___override(x_16, x_15);
x_18 = l_Lean_mkApp4(x_17, x_1, x_2, x_3, x_4);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2;
x_24 = l_Lean_Expr_const___override(x_23, x_22);
x_25 = l_Lean_mkApp4(x_24, x_1, x_2, x_3, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHEqSymm___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("heterogeneous equality types are not definitionally equal", 57);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nis not definitionally equal to", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_mkHEq___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_13 = l_Lean_indentExpr(x_1);
x_14 = l_Lean_Meta_mkEqOfHEq___closed__1;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_mkHEqTrans___closed__1;
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_18, x_17, x_2, x_3, x_4, x_5, x_9);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Expr_appFn_x21(x_8);
x_21 = l_Lean_Expr_appFn_x21(x_20);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_26 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_23);
x_27 = l_Lean_Meta_isExprDefEq(x_23, x_25, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lean_indentExpr(x_23);
x_32 = l_Lean_Meta_mkEqOfHEq___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_mkEqOfHEq___closed__5;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_indentExpr(x_25);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2;
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_40, x_39, x_2, x_3, x_4, x_5, x_30);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_25);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_dec(x_27);
x_47 = lean_box(0);
x_48 = l_Lean_Meta_mkEqOfHEq___lambda__1(x_23, x_24, x_26, x_1, x_47, x_2, x_3, x_4, x_5, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_mkEqOfHEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congrArg", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrArg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("non-dependent function expected", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrArg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkEqRefl___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_68 = l_Lean_Meta_mkEq___closed__2;
x_69 = lean_unsigned_to_nat(3u);
x_70 = l_Lean_Expr_isAppOfArity(x_11, x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_23 = x_71;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = l_Lean_Expr_appFn_x21(x_11);
x_73 = l_Lean_Expr_appFn_x21(x_72);
x_74 = l_Lean_Expr_appArg_x21(x_73);
lean_dec(x_73);
x_75 = l_Lean_Expr_appArg_x21(x_72);
lean_dec(x_72);
x_76 = l_Lean_Expr_appArg_x21(x_11);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_23 = x_79;
goto block_67;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_18 = l_Lean_Meta_mkCongrArg___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_mkCongrArg___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_15);
return x_21;
}
block_67:
{
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_14, 2);
lean_inc(x_25);
x_26 = l_Lean_Expr_hasLooseBVars(x_25);
if (x_26 == 0)
{
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_11);
x_28 = l_Lean_Meta_mkEqSymm___closed__5;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_mkCongrArg___closed__2;
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_30, x_29, x_3, x_4, x_5, x_6, x_15);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_24);
x_36 = l_Lean_Meta_getLevel(x_24, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_25);
x_39 = l_Lean_Meta_getLevel(x_25, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_mkCongrArg___closed__2;
x_46 = l_Lean_Expr_const___override(x_45, x_44);
x_47 = l_Lean_mkApp6(x_46, x_24, x_25, x_34, x_35, x_1, x_2);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_37);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_mkCongrArg___closed__2;
x_54 = l_Lean_Expr_const___override(x_53, x_52);
x_55 = l_Lean_mkApp6(x_54, x_24, x_25, x_34, x_35, x_1, x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_39);
if (x_57 == 0)
{
return x_39;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_2);
x_65 = lean_box(0);
x_16 = x_65;
goto block_22;
}
}
else
{
lean_object* x_66; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_2);
x_66 = lean_box(0);
x_16 = x_66;
goto block_22;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_13);
if (x_80 == 0)
{
return x_13;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_13, 0);
x_82 = lean_ctor_get(x_13, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_13);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_10);
if (x_84 == 0)
{
return x_10;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_89 = l_Lean_Expr_app___override(x_1, x_88);
x_90 = l_Lean_Meta_mkEqRefl(x_89, x_3, x_4, x_5, x_6, x_7);
return x_90;
}
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congrFun", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrFun___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality proof between functions expected", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrFun___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrFun___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkEqRefl___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_mkEq___closed__2;
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Expr_isAppOfArity(x_11, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_11);
x_17 = l_Lean_Meta_mkEqSymm___closed__5;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_mkCongrFun___closed__2;
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_19, x_18, x_3, x_4, x_5, x_6, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = l_Lean_Expr_appFn_x21(x_11);
x_22 = l_Lean_Expr_appFn_x21(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Expr_appArg_x21(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_Meta_whnfD(x_23, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 7)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 2);
lean_inc(x_31);
lean_dec(x_27);
x_32 = 0;
lean_inc(x_30);
x_33 = l_Lean_Expr_lam___override(x_29, x_30, x_31, x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_34 = l_Lean_Meta_getLevel(x_30, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_2);
lean_inc(x_33);
x_37 = l_Lean_Expr_app___override(x_33, x_2);
x_38 = l_Lean_Meta_getLevel(x_37, x_3, x_4, x_5, x_6, x_36);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_mkCongrFun___closed__2;
x_45 = l_Lean_Expr_const___override(x_44, x_43);
x_46 = l_Lean_mkApp6(x_45, x_30, x_33, x_24, x_25, x_1, x_2);
lean_ctor_set(x_38, 0, x_46);
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_mkCongrFun___closed__2;
x_53 = l_Lean_Expr_const___override(x_52, x_51);
x_54 = l_Lean_mkApp6(x_53, x_30, x_33, x_24, x_25, x_1, x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_38);
if (x_56 == 0)
{
return x_38;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_34);
if (x_60 == 0)
{
return x_34;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
x_64 = lean_ctor_get(x_26, 1);
lean_inc(x_64);
lean_dec(x_26);
x_65 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_11);
x_66 = l_Lean_Meta_mkCongrFun___closed__5;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_mkCongrFun___closed__2;
x_69 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_68, x_67, x_3, x_4, x_5, x_6, x_64);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_26);
if (x_70 == 0)
{
return x_26;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_26, 0);
x_72 = lean_ctor_get(x_26, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_26);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
return x_10;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_10, 0);
x_76 = lean_ctor_get(x_10, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_10);
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
x_78 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_79 = l_Lean_Expr_app___override(x_78, x_2);
x_80 = l_Lean_Meta_mkEqRefl(x_79, x_3, x_4, x_5, x_6, x_7);
return x_80;
}
}
}
static lean_object* _init_l_Lean_Meta_mkCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("congr", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkEqRefl___closed__2;
x_9 = l_Lean_Expr_isAppOf(x_1, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isAppOf(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkEq___closed__2;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
x_20 = l_Lean_Expr_isAppOfArity(x_12, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_90; 
x_90 = lean_box(0);
x_21 = x_90;
goto block_89;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_91 = l_Lean_Expr_appFn_x21(x_15);
x_92 = l_Lean_Expr_appFn_x21(x_91);
x_93 = l_Lean_Expr_appArg_x21(x_92);
lean_dec(x_92);
x_94 = l_Lean_Expr_appArg_x21(x_91);
lean_dec(x_91);
x_95 = l_Lean_Expr_appArg_x21(x_15);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_21 = x_98;
goto block_89;
}
block_89:
{
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_23 = l_Lean_Meta_mkEqSymm___closed__5;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_mkCongr___closed__2;
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_25, x_24, x_3, x_4, x_5, x_6, x_16);
return x_26;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
lean_dec(x_1);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_28 = l_Lean_Meta_mkEqSymm___closed__5;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Meta_mkCongr___closed__2;
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_30, x_29, x_3, x_4, x_5, x_6, x_16);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_15);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Expr_appFn_x21(x_12);
x_34 = l_Lean_Expr_appFn_x21(x_33);
x_35 = l_Lean_Expr_appArg_x21(x_34);
lean_dec(x_34);
x_36 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_37 = l_Lean_Expr_appArg_x21(x_12);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_42 = l_Lean_Meta_whnfD(x_35, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 7)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_dec(x_43);
x_53 = l_Lean_Expr_hasLooseBVars(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_39);
x_54 = l_Lean_Meta_getLevel(x_39, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_52);
x_57 = l_Lean_Meta_getLevel(x_52, x_3, x_4, x_5, x_6, x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_mkCongr___closed__2;
x_64 = l_Lean_Expr_const___override(x_63, x_62);
x_65 = l_Lean_mkApp8(x_64, x_39, x_52, x_36, x_37, x_40, x_41, x_1, x_2);
lean_ctor_set(x_57, 0, x_65);
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_mkCongr___closed__2;
x_72 = l_Lean_Expr_const___override(x_71, x_70);
x_73 = l_Lean_mkApp8(x_72, x_39, x_52, x_36, x_37, x_40, x_41, x_1, x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_55);
lean_dec(x_52);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_57);
if (x_75 == 0)
{
return x_57;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_57, 0);
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_57);
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
lean_dec(x_52);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_54);
if (x_79 == 0)
{
return x_54;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_54, 0);
x_81 = lean_ctor_get(x_54, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_54);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_52);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
x_83 = lean_box(0);
x_45 = x_83;
goto block_51;
}
}
else
{
lean_object* x_84; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
x_84 = lean_box(0);
x_45 = x_84;
goto block_51;
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_46 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_47 = l_Lean_Meta_mkCongrArg___closed__5;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_mkCongr___closed__2;
x_50 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_49, x_48, x_3, x_4, x_5, x_6, x_44);
return x_50;
}
}
else
{
uint8_t x_85; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_42);
if (x_85 == 0)
{
return x_42;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_42, 0);
x_87 = lean_ctor_get(x_42, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_42);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_14);
if (x_99 == 0)
{
return x_14;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_14, 0);
x_101 = lean_ctor_get(x_14, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
return x_11;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_11, 0);
x_105 = lean_ctor_get(x_11, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_11);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_108 = l_Lean_Meta_mkCongrFun(x_1, x_107, x_3, x_4, x_5, x_6, x_7);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_110 = l_Lean_Meta_mkCongrArg(x_109, x_2, x_3, x_4, x_5, x_6, x_7);
return x_110;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_getMVarDecl(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_synthInstance(x_15, x_16, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__1(x_11, x_18, x_5, x_6, x_7, x_8, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_21;
x_9 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result contains metavariables", 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_array_get_size(x_4);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
lean_dec(x_36);
x_10 = x_9;
goto block_35;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_36, x_36);
if (x_39 == 0)
{
lean_dec(x_36);
x_10 = x_9;
goto block_35;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_42 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_43 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(x_4, x_40, x_41, x_42, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_10 = x_44;
goto block_35;
}
else
{
uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_43);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
block_35:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_mkAppN(x_2, x_3);
x_12 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_11, x_5, x_6, x_7, x_8, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_15 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_indentExpr(x_13);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_1, x_25, x_5, x_6, x_7, x_8, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mkAppM", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many explicit arguments provided to", 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\narguments", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#[", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_le(x_13, x_4);
if (x_14 == 0)
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_19 = lean_array_get_size(x_6);
x_20 = lean_expr_instantiate_rev_range(x_16, x_5, x_19, x_6);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_box(x_18);
switch (lean_obj_tag(x_21)) {
case 1:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_20);
x_23 = 0;
lean_inc(x_8);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_22, x_23, x_15, x_8, x_9, x_10, x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_push(x_6, x_25);
x_3 = x_17;
x_6 = x_27;
x_12 = x_26;
goto _start;
}
case 2:
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_20);
x_30 = 0;
lean_inc(x_8);
x_31 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_29, x_30, x_15, x_8, x_9, x_10, x_11, x_12);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_push(x_6, x_32);
x_3 = x_17;
x_6 = x_34;
x_12 = x_33;
goto _start;
}
case 3:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_20);
x_37 = 1;
lean_inc(x_8);
x_38 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_37, x_15, x_8, x_9, x_10, x_11, x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_39);
x_41 = lean_array_push(x_6, x_39);
x_42 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_43 = lean_array_push(x_7, x_42);
x_3 = x_17;
x_6 = x_41;
x_7 = x_43;
x_12 = x_40;
goto _start;
}
default: 
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_15);
x_45 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13;
x_47 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_46);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_47);
x_48 = lean_infer_type(x_47, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_51 = l_Lean_Meta_isExprDefEq(x_20, x_49, x_8, x_9, x_10, x_11, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_mkAppN(x_1, x_6);
x_56 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_55, x_47, x_8, x_9, x_10, x_11, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_4, x_58);
lean_dec(x_4);
x_60 = lean_array_push(x_6, x_47);
x_3 = x_17;
x_4 = x_59;
x_6 = x_60;
x_12 = x_57;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_51);
if (x_62 == 0)
{
return x_51;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_51, 0);
x_64 = lean_ctor_get(x_51, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_51);
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
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_48);
if (x_66 == 0)
{
return x_48;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_48, 0);
x_68 = lean_ctor_get(x_48, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_array_fget(x_2, x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_70);
x_71 = lean_infer_type(x_70, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_74 = l_Lean_Meta_isExprDefEq(x_20, x_72, x_8, x_9, x_10, x_11, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = l_Lean_mkAppN(x_1, x_6);
x_79 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_78, x_70, x_8, x_9, x_10, x_11, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_4, x_81);
lean_dec(x_4);
x_83 = lean_array_push(x_6, x_70);
x_3 = x_17;
x_4 = x_82;
x_6 = x_83;
x_12 = x_80;
goto _start;
}
}
else
{
uint8_t x_85; 
lean_dec(x_70);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_74);
if (x_85 == 0)
{
return x_74;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_74, 0);
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_74);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_70);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_71);
if (x_89 == 0)
{
return x_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_71, 0);
x_91 = lean_ctor_get(x_71, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_71);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_13);
x_93 = lean_array_get_size(x_6);
x_94 = lean_expr_instantiate_rev_range(x_3, x_5, x_93, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_95 = l_Lean_Meta_whnfD(x_94, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Expr_isForall(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_99 = l_Lean_indentExpr(x_1);
x_100 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9;
x_106 = l_Lean_MessageData_arrayExpr_toMessageData(x_2, x_104, x_105);
x_107 = l_Lean_indentD(x_106);
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
x_112 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_111, x_110, x_8, x_9, x_10, x_11, x_97);
return x_112;
}
else
{
x_3 = x_96;
x_5 = x_93;
x_12 = x_97;
goto _start;
}
}
else
{
uint8_t x_114; 
lean_dec(x_93);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_95);
if (x_114 == 0)
{
return x_95;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_95, 0);
x_116 = lean_ctor_get(x_95, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_95);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
x_119 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_118, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_119;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(x_1, x_3, x_2, x_9, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_13);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Meta_mkFreshLevelMVar(x_2, x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_21, x_2, x_3, x_4, x_5, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_levelParams(x_8);
x_11 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_10, x_2, x_3, x_4, x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Expr_const___override(x_1, x_12);
x_15 = l_Lean_Core_instantiateTypeLevelParams(x_8, x_12, x_4, x_5, x_13);
lean_dec(x_8);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("constName: ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", xs: ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", result: ", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_43 = lean_st_ref_get(x_7, x_16);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_18 = x_48;
x_19 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
lean_inc(x_3);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_3, x_4, x_5, x_6, x_7, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_18 = x_53;
x_19 = x_52;
goto block_42;
}
block_42:
{
if (x_18 == 0)
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_17)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_17;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_17);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l_Lean_Meta_mkAppM___lambda__1___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_mkAppM___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_to_list(lean_box(0), x_2);
x_27 = lean_box(0);
x_28 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_26, x_27);
x_29 = l_Lean_MessageData_ofList(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_mkAppM___lambda__1___closed__6;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_15);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_15);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_3, x_36, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_15);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkAppM___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("appBuilder", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkAppM___closed__2;
x_2 = l_Lean_Meta_mkAppM___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_8 = l_Lean_Meta_mkAppM___closed__4;
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
x_225 = lean_st_ref_get(x_6, x_7);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 3);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get_uint8(x_227, sizeof(void*)*1);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
x_230 = 0;
x_10 = x_230;
x_11 = x_229;
goto block_224;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_225, 1);
lean_inc(x_231);
lean_dec(x_225);
x_232 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_8, x_3, x_4, x_5, x_6, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_unbox(x_233);
lean_dec(x_233);
x_10 = x_235;
x_11 = x_234;
goto block_224;
}
block_224:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
x_17 = lean_st_ref_take(x_6, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = 0;
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_24);
x_25 = lean_st_ref_set(x_6, x_18, x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_6);
x_27 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_6, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_take(x_6, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_33, 3);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_16);
x_39 = lean_st_ref_set(x_6, x_33, x_35);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_28);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_34, 0);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_16);
lean_ctor_set(x_33, 3, x_45);
x_46 = lean_st_ref_set(x_6, x_33, x_35);
lean_dec(x_6);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
x_52 = lean_ctor_get(x_33, 2);
x_53 = lean_ctor_get(x_33, 4);
x_54 = lean_ctor_get(x_33, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_56 = x_34;
} else {
 lean_dec_ref(x_34);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_16);
x_58 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_51);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_57);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_54);
x_59 = lean_st_ref_set(x_6, x_58, x_35);
lean_dec(x_6);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_st_ref_get(x_6, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_take(x_6, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_68, 3);
lean_dec(x_72);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_16);
x_74 = lean_st_ref_set(x_6, x_68, x_70);
lean_dec(x_6);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_63);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_63);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_16);
lean_ctor_set(x_68, 3, x_80);
x_81 = lean_st_ref_set(x_6, x_68, x_70);
lean_dec(x_6);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_63);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
x_87 = lean_ctor_get(x_68, 2);
x_88 = lean_ctor_get(x_68, 4);
x_89 = lean_ctor_get(x_68, 5);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_91 = x_69;
} else {
 lean_dec_ref(x_69);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 1, 1);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_16);
x_93 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_93, 0, x_85);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
lean_ctor_set(x_93, 3, x_92);
lean_ctor_set(x_93, 4, x_88);
lean_ctor_set(x_93, 5, x_89);
x_94 = lean_st_ref_set(x_6, x_93, x_70);
lean_dec(x_6);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
 lean_ctor_set_tag(x_97, 1);
}
lean_ctor_set(x_97, 0, x_63);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_19, 0);
lean_inc(x_98);
lean_dec(x_19);
x_99 = 0;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
lean_ctor_set(x_18, 3, x_100);
x_101 = lean_st_ref_set(x_6, x_18, x_20);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
lean_inc(x_6);
x_103 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_st_ref_get(x_6, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_st_ref_take(x_6, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_109, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_109, 5);
lean_inc(x_116);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 lean_ctor_release(x_109, 2);
 lean_ctor_release(x_109, 3);
 lean_ctor_release(x_109, 4);
 lean_ctor_release(x_109, 5);
 x_117 = x_109;
} else {
 lean_dec_ref(x_109);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_119 = x_110;
} else {
 lean_dec_ref(x_110);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 1, 1);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 6, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_113);
lean_ctor_set(x_121, 2, x_114);
lean_ctor_set(x_121, 3, x_120);
lean_ctor_set(x_121, 4, x_115);
lean_ctor_set(x_121, 5, x_116);
x_122 = lean_st_ref_set(x_6, x_121, x_111);
lean_dec(x_6);
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
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_104);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_126 = lean_ctor_get(x_103, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_103, 1);
lean_inc(x_127);
lean_dec(x_103);
x_128 = lean_st_ref_get(x_6, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_6, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_132, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_141 = x_132;
} else {
 lean_dec_ref(x_132);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_134);
lean_ctor_set(x_143, 1, x_135);
lean_ctor_set(x_143, 2, x_136);
lean_ctor_set(x_143, 3, x_142);
lean_ctor_set(x_143, 4, x_137);
lean_ctor_set(x_143, 5, x_138);
x_144 = lean_st_ref_set(x_6, x_143, x_133);
lean_dec(x_6);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_148 = lean_ctor_get(x_18, 0);
x_149 = lean_ctor_get(x_18, 1);
x_150 = lean_ctor_get(x_18, 2);
x_151 = lean_ctor_get(x_18, 4);
x_152 = lean_ctor_get(x_18, 5);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_18);
x_153 = lean_ctor_get(x_19, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_154 = x_19;
} else {
 lean_dec_ref(x_19);
 x_154 = lean_box(0);
}
x_155 = 0;
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 1, 1);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_155);
x_157 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_156);
lean_ctor_set(x_157, 4, x_151);
lean_ctor_set(x_157, 5, x_152);
x_158 = lean_st_ref_set(x_6, x_157, x_20);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_inc(x_6);
x_160 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_3, x_4, x_5, x_6, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_6, x_162);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_st_ref_take(x_6, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_166, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_166, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_166, 5);
lean_inc(x_173);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 lean_ctor_release(x_166, 4);
 lean_ctor_release(x_166, 5);
 x_174 = x_166;
} else {
 lean_dec_ref(x_166);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_167, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_176 = x_167;
} else {
 lean_dec_ref(x_167);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 1, 1);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 6, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_169);
lean_ctor_set(x_178, 1, x_170);
lean_ctor_set(x_178, 2, x_171);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set(x_178, 4, x_172);
lean_ctor_set(x_178, 5, x_173);
x_179 = lean_st_ref_set(x_6, x_178, x_168);
lean_dec(x_6);
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
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_161);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_183 = lean_ctor_get(x_160, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_160, 1);
lean_inc(x_184);
lean_dec(x_160);
x_185 = lean_st_ref_get(x_6, x_184);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_st_ref_take(x_6, x_186);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 1, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_16);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_191);
lean_ctor_set(x_200, 1, x_192);
lean_ctor_set(x_200, 2, x_193);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_200, 4, x_194);
lean_ctor_set(x_200, 5, x_195);
x_201 = lean_st_ref_set(x_6, x_200, x_190);
lean_dec(x_6);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
 lean_ctor_set_tag(x_204, 1);
}
lean_ctor_set(x_204, 0, x_183);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_5, 5);
lean_inc(x_205);
x_206 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_6, x_11);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_209 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_9, x_3, x_4, x_5, x_6, x_208);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_207, x_8, x_205, x_3, x_4, x_5, x_6, x_211);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
lean_ctor_set(x_212, 0, x_210);
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_209, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_209, 1);
lean_inc(x_218);
lean_dec(x_209);
x_219 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_207, x_8, x_205, x_3, x_4, x_5, x_6, x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_219, 0);
lean_dec(x_221);
lean_ctor_set_tag(x_219, 1);
lean_ctor_set(x_219, 0, x_217);
return x_219;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAppM_x27___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("f: ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAppM_x27___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkAppM_x27___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_39 = lean_st_ref_get(x_8, x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 3);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = 0;
x_14 = x_44;
x_15 = x_43;
goto block_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
lean_inc(x_4);
x_46 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_4, x_5, x_6, x_7, x_8, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unbox(x_47);
lean_dec(x_47);
x_14 = x_49;
x_15 = x_48;
goto block_38;
}
block_38:
{
if (x_14 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_13);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_Meta_mkAppM_x27___lambda__1___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_mkAppM___lambda__1___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_to_list(lean_box(0), x_3);
x_23 = lean_box(0);
x_24 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_mkAppM___lambda__1___closed__6;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_11);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_11);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_32, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_11);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_mkAppM___closed__4;
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM_x27___lambda__1), 9, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
x_228 = lean_st_ref_get(x_6, x_10);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 3);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_ctor_get_uint8(x_230, sizeof(void*)*1);
lean_dec(x_230);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_228, 1);
lean_inc(x_232);
lean_dec(x_228);
x_233 = 0;
x_13 = x_233;
x_14 = x_232;
goto block_227;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
lean_dec(x_228);
x_235 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_11, x_3, x_4, x_5, x_6, x_234);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
x_238 = lean_unbox(x_236);
lean_dec(x_236);
x_13 = x_238;
x_14 = x_237;
goto block_227;
}
block_227:
{
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_6, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 3);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_27);
x_28 = lean_st_ref_set(x_6, x_21, x_23);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_6);
x_30 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_6, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_take(x_6, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 3);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_19);
x_42 = lean_st_ref_set(x_6, x_36, x_38);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_31);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_19);
lean_ctor_set(x_36, 3, x_48);
x_49 = lean_st_ref_set(x_6, x_36, x_38);
lean_dec(x_6);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
x_55 = lean_ctor_get(x_36, 2);
x_56 = lean_ctor_get(x_36, 4);
x_57 = lean_ctor_get(x_36, 5);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_58 = lean_ctor_get(x_37, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 1);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_19);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_56);
lean_ctor_set(x_61, 5, x_57);
x_62 = lean_st_ref_set(x_6, x_61, x_38);
lean_dec(x_6);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_31);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_ctor_get(x_30, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 1);
lean_inc(x_67);
lean_dec(x_30);
x_68 = lean_st_ref_get(x_6, x_67);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_st_ref_take(x_6, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 3);
lean_dec(x_75);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_19);
x_77 = lean_st_ref_set(x_6, x_71, x_73);
lean_dec(x_6);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_66);
return x_77;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_72, 0);
lean_inc(x_82);
lean_dec(x_72);
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_19);
lean_ctor_set(x_71, 3, x_83);
x_84 = lean_st_ref_set(x_6, x_71, x_73);
lean_dec(x_6);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
 lean_ctor_set_tag(x_87, 1);
}
lean_ctor_set(x_87, 0, x_66);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_88 = lean_ctor_get(x_71, 0);
x_89 = lean_ctor_get(x_71, 1);
x_90 = lean_ctor_get(x_71, 2);
x_91 = lean_ctor_get(x_71, 4);
x_92 = lean_ctor_get(x_71, 5);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_71);
x_93 = lean_ctor_get(x_72, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_94 = x_72;
} else {
 lean_dec_ref(x_72);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 1, 1);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_19);
x_96 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_96, 0, x_88);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_90);
lean_ctor_set(x_96, 3, x_95);
lean_ctor_set(x_96, 4, x_91);
lean_ctor_set(x_96, 5, x_92);
x_97 = lean_st_ref_set(x_6, x_96, x_73);
lean_dec(x_6);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
 lean_ctor_set_tag(x_100, 1);
}
lean_ctor_set(x_100, 0, x_66);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_22, 0);
lean_inc(x_101);
lean_dec(x_22);
x_102 = 0;
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_102);
lean_ctor_set(x_21, 3, x_103);
x_104 = lean_st_ref_set(x_6, x_21, x_23);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc(x_6);
x_106 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_st_ref_get(x_6, x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_take(x_6, x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 4);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 5);
lean_inc(x_119);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 x_120 = x_112;
} else {
 lean_dec_ref(x_112);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 1, 1);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_19);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(0, 6, 0);
} else {
 x_124 = x_120;
}
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_116);
lean_ctor_set(x_124, 2, x_117);
lean_ctor_set(x_124, 3, x_123);
lean_ctor_set(x_124, 4, x_118);
lean_ctor_set(x_124, 5, x_119);
x_125 = lean_st_ref_set(x_6, x_124, x_114);
lean_dec(x_6);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_107);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_129 = lean_ctor_get(x_106, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_106, 1);
lean_inc(x_130);
lean_dec(x_106);
x_131 = lean_st_ref_get(x_6, x_130);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_6, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_134, 5);
lean_inc(x_141);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 lean_ctor_release(x_134, 4);
 lean_ctor_release(x_134, 5);
 x_142 = x_134;
} else {
 lean_dec_ref(x_134);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 1);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_19);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(0, 6, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_138);
lean_ctor_set(x_146, 2, x_139);
lean_ctor_set(x_146, 3, x_145);
lean_ctor_set(x_146, 4, x_140);
lean_ctor_set(x_146, 5, x_141);
x_147 = lean_st_ref_set(x_6, x_146, x_136);
lean_dec(x_6);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_129);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_151 = lean_ctor_get(x_21, 0);
x_152 = lean_ctor_get(x_21, 1);
x_153 = lean_ctor_get(x_21, 2);
x_154 = lean_ctor_get(x_21, 4);
x_155 = lean_ctor_get(x_21, 5);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_21);
x_156 = lean_ctor_get(x_22, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_157 = x_22;
} else {
 lean_dec_ref(x_22);
 x_157 = lean_box(0);
}
x_158 = 0;
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 1, 1);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_160, 0, x_151);
lean_ctor_set(x_160, 1, x_152);
lean_ctor_set(x_160, 2, x_153);
lean_ctor_set(x_160, 3, x_159);
lean_ctor_set(x_160, 4, x_154);
lean_ctor_set(x_160, 5, x_155);
x_161 = lean_st_ref_set(x_6, x_160, x_23);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_6);
x_163 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_st_ref_get(x_6, x_165);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_st_ref_take(x_6, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_169, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 5);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_179 = x_170;
} else {
 lean_dec_ref(x_170);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 1, 1);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_19);
if (lean_is_scalar(x_177)) {
 x_181 = lean_alloc_ctor(0, 6, 0);
} else {
 x_181 = x_177;
}
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_173);
lean_ctor_set(x_181, 2, x_174);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set(x_181, 4, x_175);
lean_ctor_set(x_181, 5, x_176);
x_182 = lean_st_ref_set(x_6, x_181, x_171);
lean_dec(x_6);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_184 = x_182;
} else {
 lean_dec_ref(x_182);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_164);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_186 = lean_ctor_get(x_163, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_163, 1);
lean_inc(x_187);
lean_dec(x_163);
x_188 = lean_st_ref_get(x_6, x_187);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_st_ref_take(x_6, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_191, 2);
lean_inc(x_196);
x_197 = lean_ctor_get(x_191, 4);
lean_inc(x_197);
x_198 = lean_ctor_get(x_191, 5);
lean_inc(x_198);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 lean_ctor_release(x_191, 2);
 lean_ctor_release(x_191, 3);
 lean_ctor_release(x_191, 4);
 lean_ctor_release(x_191, 5);
 x_199 = x_191;
} else {
 lean_dec_ref(x_191);
 x_199 = lean_box(0);
}
x_200 = lean_ctor_get(x_192, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_201 = x_192;
} else {
 lean_dec_ref(x_192);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 1, 1);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1, x_19);
if (lean_is_scalar(x_199)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_199;
}
lean_ctor_set(x_203, 0, x_194);
lean_ctor_set(x_203, 1, x_195);
lean_ctor_set(x_203, 2, x_196);
lean_ctor_set(x_203, 3, x_202);
lean_ctor_set(x_203, 4, x_197);
lean_ctor_set(x_203, 5, x_198);
x_204 = lean_st_ref_set(x_6, x_203, x_193);
lean_dec(x_6);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
 lean_ctor_set_tag(x_207, 1);
}
lean_ctor_set(x_207, 0, x_186);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_5, 5);
lean_inc(x_208);
x_209 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_6, x_14);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_212 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_12, x_3, x_4, x_5, x_6, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_210, x_11, x_208, x_3, x_4, x_5, x_6, x_214);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_215, 0);
lean_dec(x_217);
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_213);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_212, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_212, 1);
lean_inc(x_221);
lean_dec(x_212);
x_222 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_210, x_11, x_208, x_3, x_4, x_5, x_6, x_221);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_222, 0);
lean_dec(x_224);
lean_ctor_set_tag(x_222, 1);
lean_ctor_set(x_222, 0, x_220);
return x_222;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_8);
if (x_239 == 0)
{
return x_8;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_8, 0);
x_241 = lean_ctor_get(x_8, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_8);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_push(x_4, x_10);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mkAppOptM", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many arguments provided to", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("arguments", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9;
x_4 = l_Lean_MessageData_arrayExpr_toMessageData(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_17 = lean_array_get_size(x_4);
x_18 = lean_expr_instantiate_rev_range(x_14, x_5, x_17, x_4);
lean_dec(x_17);
lean_dec(x_14);
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_lt(x_3, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_21, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_box(x_16);
if (lean_obj_tag(x_24) == 3)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_18);
x_26 = 1;
lean_inc(x_8);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_25, x_26, x_13, x_8, x_9, x_10, x_11, x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
lean_inc(x_28);
x_32 = lean_array_push(x_4, x_28);
x_33 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
x_34 = lean_array_push(x_6, x_33);
x_3 = x_31;
x_4 = x_32;
x_6 = x_34;
x_7 = x_15;
x_12 = x_29;
goto _start;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_24);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_18);
x_37 = 0;
lean_inc(x_8);
x_38 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_36, x_37, x_13, x_8, x_9, x_10, x_11, x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_3, x_41);
lean_dec(x_3);
x_43 = lean_array_push(x_4, x_39);
x_3 = x_42;
x_4 = x_43;
x_7 = x_15;
x_12 = x_40;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
x_45 = lean_ctor_get(x_23, 0);
lean_inc(x_45);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_45);
x_46 = lean_infer_type(x_45, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_Meta_isExprDefEq(x_18, x_47, x_8, x_9, x_10, x_11, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_mkAppN(x_1, x_4);
x_54 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_53, x_45, x_8, x_9, x_10, x_11, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_dec(x_49);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_3, x_56);
lean_dec(x_3);
x_58 = lean_array_push(x_4, x_45);
x_3 = x_57;
x_4 = x_58;
x_7 = x_15;
x_12 = x_55;
goto _start;
}
}
else
{
uint8_t x_60; 
lean_dec(x_45);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_49);
if (x_60 == 0)
{
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_45);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_46);
if (x_64 == 0)
{
return x_46;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_46, 0);
x_66 = lean_ctor_get(x_46, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_46);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_array_get_size(x_4);
x_69 = lean_expr_instantiate_rev_range(x_7, x_5, x_68, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_70 = l_Lean_Meta_whnfD(x_69, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_isForall(x_71);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_71);
lean_dec(x_68);
x_74 = lean_array_get_size(x_2);
x_75 = lean_nat_dec_eq(x_3, x_74);
lean_dec(x_3);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_6);
lean_dec(x_4);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_74);
x_78 = l_Lean_indentExpr(x_1);
x_79 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
if (x_77 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
x_85 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_88 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_87, x_86, x_8, x_9, x_10, x_11, x_72);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_nat_dec_le(x_74, x_74);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_74);
x_90 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_90);
x_92 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_93 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_92, x_91, x_8, x_9, x_10, x_11, x_72);
return x_93;
}
else
{
size_t x_94; size_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = 0;
x_95 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_96 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
x_97 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(x_2, x_94, x_95, x_96);
x_98 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9;
x_99 = l_Lean_MessageData_arrayExpr_toMessageData(x_97, x_76, x_98);
lean_dec(x_97);
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_84);
lean_ctor_set(x_100, 1, x_99);
x_101 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_102 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_101, x_100, x_8, x_9, x_10, x_11, x_72);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_74);
x_103 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
x_104 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_103, x_1, x_4, x_6, x_8, x_9, x_10, x_11, x_72);
lean_dec(x_6);
return x_104;
}
}
else
{
x_5 = x_68;
x_7 = x_71;
x_12 = x_72;
goto _start;
}
}
else
{
uint8_t x_106; 
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_70);
if (x_106 == 0)
{
return x_70;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_70, 0);
x_108 = lean_ctor_get(x_70, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_70);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(x_11, x_2, x_13, x_14, x_13, x_14, x_12, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lambda__1___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_226 = lean_st_ref_get(x_6, x_7);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_227, 3);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_ctor_get_uint8(x_228, sizeof(void*)*1);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; uint8_t x_231; 
x_230 = lean_ctor_get(x_226, 1);
lean_inc(x_230);
lean_dec(x_226);
x_231 = 0;
x_9 = x_231;
x_10 = x_230;
goto block_225;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_232 = lean_ctor_get(x_226, 1);
lean_inc(x_232);
lean_dec(x_226);
x_233 = l_Lean_Meta_mkAppM___closed__4;
x_234 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_233, x_3, x_4, x_5, x_6, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_unbox(x_235);
lean_dec(x_235);
x_9 = x_237;
x_10 = x_236;
goto block_225;
}
block_225:
{
if (x_9 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_st_ref_get(x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = 0;
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_23);
x_24 = lean_st_ref_set(x_6, x_17, x_19);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_6);
x_26 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_8, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_6, x_28);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_6, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_32, 3);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_15);
x_38 = lean_st_ref_set(x_6, x_32, x_34);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_27);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_15);
lean_ctor_set(x_32, 3, x_44);
x_45 = lean_st_ref_set(x_6, x_32, x_34);
lean_dec(x_6);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_27);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
x_51 = lean_ctor_get(x_32, 2);
x_52 = lean_ctor_get(x_32, 4);
x_53 = lean_ctor_get(x_32, 5);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_55 = x_33;
} else {
 lean_dec_ref(x_33);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_15);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_51);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_53);
x_58 = lean_st_ref_set(x_6, x_57, x_34);
lean_dec(x_6);
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
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_27);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_26, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_26, 1);
lean_inc(x_63);
lean_dec(x_26);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_6, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 3);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_15);
x_73 = lean_st_ref_set(x_6, x_67, x_69);
lean_dec(x_6);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_62);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_15);
lean_ctor_set(x_67, 3, x_79);
x_80 = lean_st_ref_set(x_6, x_67, x_69);
lean_dec(x_6);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
x_86 = lean_ctor_get(x_67, 2);
x_87 = lean_ctor_get(x_67, 4);
x_88 = lean_ctor_get(x_67, 5);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_89 = lean_ctor_get(x_68, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_90 = x_68;
} else {
 lean_dec_ref(x_68);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 1, 1);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_15);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_84);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_91);
lean_ctor_set(x_92, 4, x_87);
lean_ctor_set(x_92, 5, x_88);
x_93 = lean_st_ref_set(x_6, x_92, x_69);
lean_dec(x_6);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_95 = x_93;
} else {
 lean_dec_ref(x_93);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
 lean_ctor_set_tag(x_96, 1);
}
lean_ctor_set(x_96, 0, x_62);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_18, 0);
lean_inc(x_97);
lean_dec(x_18);
x_98 = 0;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
lean_ctor_set(x_17, 3, x_99);
x_100 = lean_st_ref_set(x_6, x_17, x_19);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_6);
x_102 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_8, x_3, x_4, x_5, x_6, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_st_ref_get(x_6, x_104);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_st_ref_take(x_6, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_ctor_get(x_108, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_108, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_108, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 5);
lean_inc(x_115);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 lean_ctor_release(x_108, 5);
 x_116 = x_108;
} else {
 lean_dec_ref(x_108);
 x_116 = lean_box(0);
}
x_117 = lean_ctor_get(x_109, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 1, 1);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_116)) {
 x_120 = lean_alloc_ctor(0, 6, 0);
} else {
 x_120 = x_116;
}
lean_ctor_set(x_120, 0, x_111);
lean_ctor_set(x_120, 1, x_112);
lean_ctor_set(x_120, 2, x_113);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_114);
lean_ctor_set(x_120, 5, x_115);
x_121 = lean_st_ref_set(x_6, x_120, x_110);
lean_dec(x_6);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_123 = x_121;
} else {
 lean_dec_ref(x_121);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_103);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_125 = lean_ctor_get(x_102, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_102, 1);
lean_inc(x_126);
lean_dec(x_102);
x_127 = lean_st_ref_get(x_6, x_126);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_st_ref_take(x_6, x_128);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_130, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 5);
lean_inc(x_137);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 lean_ctor_release(x_130, 2);
 lean_ctor_release(x_130, 3);
 lean_ctor_release(x_130, 4);
 lean_ctor_release(x_130, 5);
 x_138 = x_130;
} else {
 lean_dec_ref(x_130);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_131, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_140 = x_131;
} else {
 lean_dec_ref(x_131);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 1, 1);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_138)) {
 x_142 = lean_alloc_ctor(0, 6, 0);
} else {
 x_142 = x_138;
}
lean_ctor_set(x_142, 0, x_133);
lean_ctor_set(x_142, 1, x_134);
lean_ctor_set(x_142, 2, x_135);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set(x_142, 4, x_136);
lean_ctor_set(x_142, 5, x_137);
x_143 = lean_st_ref_set(x_6, x_142, x_132);
lean_dec(x_6);
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_125);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_147 = lean_ctor_get(x_17, 0);
x_148 = lean_ctor_get(x_17, 1);
x_149 = lean_ctor_get(x_17, 2);
x_150 = lean_ctor_get(x_17, 4);
x_151 = lean_ctor_get(x_17, 5);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_17);
x_152 = lean_ctor_get(x_18, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_153 = x_18;
} else {
 lean_dec_ref(x_18);
 x_153 = lean_box(0);
}
x_154 = 0;
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 1, 1);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_156, 0, x_147);
lean_ctor_set(x_156, 1, x_148);
lean_ctor_set(x_156, 2, x_149);
lean_ctor_set(x_156, 3, x_155);
lean_ctor_set(x_156, 4, x_150);
lean_ctor_set(x_156, 5, x_151);
x_157 = lean_st_ref_set(x_6, x_156, x_19);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
lean_inc(x_6);
x_159 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_8, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_st_ref_get(x_6, x_161);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_st_ref_take(x_6, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 3);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_168 = lean_ctor_get(x_165, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_165, 5);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 lean_ctor_release(x_165, 5);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_166, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_175 = x_166;
} else {
 lean_dec_ref(x_166);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 1, 1);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set_uint8(x_176, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_169);
lean_ctor_set(x_177, 2, x_170);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set(x_177, 4, x_171);
lean_ctor_set(x_177, 5, x_172);
x_178 = lean_st_ref_set(x_6, x_177, x_167);
lean_dec(x_6);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_160);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_182 = lean_ctor_get(x_159, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_159, 1);
lean_inc(x_183);
lean_dec(x_159);
x_184 = lean_st_ref_get(x_6, x_183);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_st_ref_take(x_6, x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_187, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 2);
lean_inc(x_192);
x_193 = lean_ctor_get(x_187, 4);
lean_inc(x_193);
x_194 = lean_ctor_get(x_187, 5);
lean_inc(x_194);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 lean_ctor_release(x_187, 5);
 x_195 = x_187;
} else {
 lean_dec_ref(x_187);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_188, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 1, 1);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_15);
if (lean_is_scalar(x_195)) {
 x_199 = lean_alloc_ctor(0, 6, 0);
} else {
 x_199 = x_195;
}
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_191);
lean_ctor_set(x_199, 2, x_192);
lean_ctor_set(x_199, 3, x_198);
lean_ctor_set(x_199, 4, x_193);
lean_ctor_set(x_199, 5, x_194);
x_200 = lean_st_ref_set(x_6, x_199, x_189);
lean_dec(x_6);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_5, 5);
lean_inc(x_204);
x_205 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_6, x_10);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_208 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_8, x_3, x_4, x_5, x_6, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Meta_mkAppM___closed__4;
x_212 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_206, x_211, x_204, x_3, x_4, x_5, x_6, x_210);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_212, 0);
lean_dec(x_214);
lean_ctor_set(x_212, 0, x_209);
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_212, 1);
lean_inc(x_215);
lean_dec(x_212);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_209);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_ctor_get(x_208, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_208, 1);
lean_inc(x_218);
lean_dec(x_208);
x_219 = l_Lean_Meta_mkAppM___closed__4;
x_220 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_206, x_219, x_204, x_3, x_4, x_5, x_6, x_218);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_220, 0);
lean_dec(x_222);
lean_ctor_set_tag(x_220, 1);
lean_ctor_set(x_220, 0, x_217);
return x_220;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_217);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppOptM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
lean_closure_set(x_13, 6, x_9);
x_231 = lean_st_ref_get(x_6, x_10);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_232, 3);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get_uint8(x_233, sizeof(void*)*1);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
lean_dec(x_231);
x_236 = 0;
x_14 = x_236;
x_15 = x_235;
goto block_230;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
lean_dec(x_231);
x_238 = l_Lean_Meta_mkAppM___closed__4;
x_239 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_238, x_3, x_4, x_5, x_6, x_237);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_unbox(x_240);
lean_dec(x_240);
x_14 = x_242;
x_15 = x_241;
goto block_230;
}
block_230:
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_st_ref_get(x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
x_21 = lean_st_ref_take(x_6, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 3);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = 0;
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_28);
x_29 = lean_st_ref_set(x_6, x_22, x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_6);
x_31 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_6, x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_37, 3);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_20);
x_43 = lean_st_ref_set(x_6, x_37, x_39);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_20);
lean_ctor_set(x_37, 3, x_49);
x_50 = lean_st_ref_set(x_6, x_37, x_39);
lean_dec(x_6);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_32);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
x_56 = lean_ctor_get(x_37, 2);
x_57 = lean_ctor_get(x_37, 4);
x_58 = lean_ctor_get(x_37, 5);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_59 = lean_ctor_get(x_38, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_60 = x_38;
} else {
 lean_dec_ref(x_38);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 1, 1);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_20);
x_62 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_55);
lean_ctor_set(x_62, 2, x_56);
lean_ctor_set(x_62, 3, x_61);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
x_63 = lean_st_ref_set(x_6, x_62, x_39);
lean_dec(x_6);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_32);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_31, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_31, 1);
lean_inc(x_68);
lean_dec(x_31);
x_69 = lean_st_ref_get(x_6, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_take(x_6, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_72, 3);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_20);
x_78 = lean_st_ref_set(x_6, x_72, x_74);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_dec(x_80);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 0, x_67);
return x_78;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_73, 0);
lean_inc(x_83);
lean_dec(x_73);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_20);
lean_ctor_set(x_72, 3, x_84);
x_85 = lean_st_ref_set(x_6, x_72, x_74);
lean_dec(x_6);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
 lean_ctor_set_tag(x_88, 1);
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_72, 0);
x_90 = lean_ctor_get(x_72, 1);
x_91 = lean_ctor_get(x_72, 2);
x_92 = lean_ctor_get(x_72, 4);
x_93 = lean_ctor_get(x_72, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_72);
x_94 = lean_ctor_get(x_73, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_95 = x_73;
} else {
 lean_dec_ref(x_73);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_20);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_92);
lean_ctor_set(x_97, 5, x_93);
x_98 = lean_st_ref_set(x_6, x_97, x_74);
lean_dec(x_6);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_67);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_23, 0);
lean_inc(x_102);
lean_dec(x_23);
x_103 = 0;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
lean_ctor_set(x_22, 3, x_104);
x_105 = lean_st_ref_set(x_6, x_22, x_24);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_6);
x_107 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_st_ref_get(x_6, x_109);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_st_ref_take(x_6, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_123 = x_114;
} else {
 lean_dec_ref(x_114);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 1, 1);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_121)) {
 x_125 = lean_alloc_ctor(0, 6, 0);
} else {
 x_125 = x_121;
}
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_118);
lean_ctor_set(x_125, 3, x_124);
lean_ctor_set(x_125, 4, x_119);
lean_ctor_set(x_125, 5, x_120);
x_126 = lean_st_ref_set(x_6, x_125, x_115);
lean_dec(x_6);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_108);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_130 = lean_ctor_get(x_107, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_107, 1);
lean_inc(x_131);
lean_dec(x_107);
x_132 = lean_st_ref_get(x_6, x_131);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_st_ref_take(x_6, x_133);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_135, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_135, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_135, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 5);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_136, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_145 = x_136;
} else {
 lean_dec_ref(x_136);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 1, 1);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 6, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_138);
lean_ctor_set(x_147, 1, x_139);
lean_ctor_set(x_147, 2, x_140);
lean_ctor_set(x_147, 3, x_146);
lean_ctor_set(x_147, 4, x_141);
lean_ctor_set(x_147, 5, x_142);
x_148 = lean_st_ref_set(x_6, x_147, x_137);
lean_dec(x_6);
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
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_130);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_152 = lean_ctor_get(x_22, 0);
x_153 = lean_ctor_get(x_22, 1);
x_154 = lean_ctor_get(x_22, 2);
x_155 = lean_ctor_get(x_22, 4);
x_156 = lean_ctor_get(x_22, 5);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_22);
x_157 = lean_ctor_get(x_23, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_158 = x_23;
} else {
 lean_dec_ref(x_23);
 x_158 = lean_box(0);
}
x_159 = 0;
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 1, 1);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
x_161 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_160);
lean_ctor_set(x_161, 4, x_155);
lean_ctor_set(x_161, 5, x_156);
x_162 = lean_st_ref_set(x_6, x_161, x_24);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_6);
x_164 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_st_ref_get(x_6, x_166);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_ref_take(x_6, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_170, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_170, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_170, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 lean_ctor_release(x_170, 2);
 lean_ctor_release(x_170, 3);
 lean_ctor_release(x_170, 4);
 lean_ctor_release(x_170, 5);
 x_178 = x_170;
} else {
 lean_dec_ref(x_170);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_171, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 6, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_173);
lean_ctor_set(x_182, 1, x_174);
lean_ctor_set(x_182, 2, x_175);
lean_ctor_set(x_182, 3, x_181);
lean_ctor_set(x_182, 4, x_176);
lean_ctor_set(x_182, 5, x_177);
x_183 = lean_st_ref_set(x_6, x_182, x_172);
lean_dec(x_6);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_165);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_187 = lean_ctor_get(x_164, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_164, 1);
lean_inc(x_188);
lean_dec(x_164);
x_189 = lean_st_ref_get(x_6, x_188);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_st_ref_take(x_6, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_192, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 2);
lean_inc(x_197);
x_198 = lean_ctor_get(x_192, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_192, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 lean_ctor_release(x_192, 2);
 lean_ctor_release(x_192, 3);
 lean_ctor_release(x_192, 4);
 lean_ctor_release(x_192, 5);
 x_200 = x_192;
} else {
 lean_dec_ref(x_192);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_202 = x_193;
} else {
 lean_dec_ref(x_193);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 1, 1);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_20);
if (lean_is_scalar(x_200)) {
 x_204 = lean_alloc_ctor(0, 6, 0);
} else {
 x_204 = x_200;
}
lean_ctor_set(x_204, 0, x_195);
lean_ctor_set(x_204, 1, x_196);
lean_ctor_set(x_204, 2, x_197);
lean_ctor_set(x_204, 3, x_203);
lean_ctor_set(x_204, 4, x_198);
lean_ctor_set(x_204, 5, x_199);
x_205 = lean_st_ref_set(x_6, x_204, x_194);
lean_dec(x_6);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
 lean_ctor_set_tag(x_208, 1);
}
lean_ctor_set(x_208, 0, x_187);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_209 = lean_ctor_get(x_5, 5);
lean_inc(x_209);
x_210 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__7___rarg(x_6, x_15);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_213 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(x_13, x_3, x_4, x_5, x_6, x_212);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = l_Lean_Meta_mkAppM___closed__4;
x_217 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_211, x_216, x_209, x_3, x_4, x_5, x_6, x_215);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
lean_ctor_set(x_217, 0, x_214);
return x_217;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_214);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_213, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
lean_dec(x_213);
x_224 = l_Lean_Meta_mkAppM___closed__4;
x_225 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__13(x_211, x_224, x_209, x_3, x_4, x_5, x_6, x_223);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_225, 0);
lean_dec(x_227);
lean_ctor_set_tag(x_225, 1);
lean_ctor_set(x_225, 0, x_222);
return x_225;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_222);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_8);
if (x_243 == 0)
{
return x_8;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_8, 0);
x_245 = lean_ctor_get(x_8, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_8);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ndrec", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqNDRec___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid motive", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqNDRec___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqNDRec___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_mkEqRefl___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEq___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_3, x_12);
x_18 = l_Lean_Meta_mkEqSymm___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_mkEqNDRec___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_27 = l_Lean_Meta_getLevel(x_24, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 3)
{
uint8_t x_33; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_mkEqNDRec___closed__2;
x_40 = l_Lean_Expr_const___override(x_39, x_38);
x_41 = l_Lean_Meta_mkEqNDRec___closed__6;
x_42 = lean_array_push(x_41, x_24);
x_43 = lean_array_push(x_42, x_25);
x_44 = lean_array_push(x_43, x_1);
x_45 = lean_array_push(x_44, x_2);
x_46 = lean_array_push(x_45, x_26);
x_47 = lean_array_push(x_46, x_3);
x_48 = l_Lean_mkAppN(x_40, x_47);
lean_ctor_set(x_30, 0, x_48);
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
lean_dec(x_32);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_28);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_mkEqNDRec___closed__2;
x_55 = l_Lean_Expr_const___override(x_54, x_53);
x_56 = l_Lean_Meta_mkEqNDRec___closed__6;
x_57 = lean_array_push(x_56, x_24);
x_58 = lean_array_push(x_57, x_25);
x_59 = lean_array_push(x_58, x_1);
x_60 = lean_array_push(x_59, x_2);
x_61 = lean_array_push(x_60, x_26);
x_62 = lean_array_push(x_61, x_3);
x_63 = l_Lean_mkAppN(x_55, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_49);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_30, 1);
lean_inc(x_65);
lean_dec(x_30);
x_66 = l_Lean_indentExpr(x_1);
x_67 = l_Lean_Meta_mkEqNDRec___closed__5;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Meta_mkEqNDRec___closed__2;
x_70 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_69, x_68, x_4, x_5, x_6, x_7, x_65);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_dec(x_30);
x_72 = l_Lean_indentExpr(x_1);
x_73 = l_Lean_Meta_mkEqNDRec___closed__5;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Meta_mkEqNDRec___closed__2;
x_76 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_75, x_74, x_4, x_5, x_6, x_7, x_71);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_30);
if (x_77 == 0)
{
return x_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_30, 0);
x_79 = lean_ctor_get(x_30, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_30);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_27);
if (x_81 == 0)
{
return x_27;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_27, 0);
x_83 = lean_ctor_get(x_27, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_27);
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
uint8_t x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_11);
if (x_85 == 0)
{
return x_11;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_11, 0);
x_87 = lean_ctor_get(x_11, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_11);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_8);
return x_89;
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqRec___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_mkEqRefl___closed__2;
x_10 = l_Lean_Expr_isAppOf(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEq___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_indentExpr(x_3);
x_18 = l_Lean_Meta_mkEqSymm___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_mkEqRec___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_4, x_5, x_6, x_7, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_24);
x_27 = l_Lean_Meta_getLevel(x_24, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(x_1, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 7)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 7)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 3)
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_mkEqRec___closed__2;
x_41 = l_Lean_Expr_const___override(x_40, x_39);
x_42 = l_Lean_Meta_mkEqNDRec___closed__6;
x_43 = lean_array_push(x_42, x_24);
x_44 = lean_array_push(x_43, x_25);
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_2);
x_47 = lean_array_push(x_46, x_26);
x_48 = lean_array_push(x_47, x_3);
x_49 = l_Lean_mkAppN(x_41, x_48);
lean_ctor_set(x_30, 0, x_49);
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_dec(x_30);
x_51 = lean_ctor_get(x_33, 0);
lean_inc(x_51);
lean_dec(x_33);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_28);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Meta_mkEqRec___closed__2;
x_56 = l_Lean_Expr_const___override(x_55, x_54);
x_57 = l_Lean_Meta_mkEqNDRec___closed__6;
x_58 = lean_array_push(x_57, x_24);
x_59 = lean_array_push(x_58, x_25);
x_60 = lean_array_push(x_59, x_1);
x_61 = lean_array_push(x_60, x_2);
x_62 = lean_array_push(x_61, x_26);
x_63 = lean_array_push(x_62, x_3);
x_64 = l_Lean_mkAppN(x_56, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_30, 1);
lean_inc(x_66);
lean_dec(x_30);
x_67 = l_Lean_indentExpr(x_1);
x_68 = l_Lean_Meta_mkEqNDRec___closed__5;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Lean_Meta_mkEqRec___closed__2;
x_71 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_70, x_69, x_4, x_5, x_6, x_7, x_66);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
lean_dec(x_30);
x_73 = l_Lean_indentExpr(x_1);
x_74 = l_Lean_Meta_mkEqNDRec___closed__5;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Meta_mkEqRec___closed__2;
x_77 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_76, x_75, x_4, x_5, x_6, x_7, x_72);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_30, 1);
lean_inc(x_78);
lean_dec(x_30);
x_79 = l_Lean_indentExpr(x_1);
x_80 = l_Lean_Meta_mkEqNDRec___closed__5;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Meta_mkEqRec___closed__2;
x_83 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_82, x_81, x_4, x_5, x_6, x_7, x_78);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_30);
if (x_84 == 0)
{
return x_30;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_30, 0);
x_86 = lean_ctor_get(x_30, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_30);
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
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_27);
if (x_88 == 0)
{
return x_27;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_27, 0);
x_90 = lean_ctor_get(x_27, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_27);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_11);
if (x_92 == 0)
{
return x_11;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_11, 0);
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_11);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_8);
return x_96;
}
}
}
static lean_object* _init_l_Lean_Meta_mkEqMP___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mp", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMP___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqMP___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMP___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkEqMP___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMPR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mpr", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqMPR___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkEq___closed__2;
x_2 = l_Lean_Meta_mkEqMPR___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkEqMPR___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("noConfusion", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkNoConfusion___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality expected", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inductive type expected", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_infer_type(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_mkEq___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_12);
x_18 = l_Lean_Meta_mkNoConfusion___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Meta_mkNoConfusion___closed__2;
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_20, x_19, x_3, x_4, x_5, x_6, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_Expr_appFn_x21(x_12);
x_23 = l_Lean_Expr_appFn_x21(x_22);
x_24 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_26 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Meta_whnfD(x_24, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_6, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_environment_find(x_36, x_31);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_38 = l_Lean_indentExpr(x_28);
x_39 = l_Lean_Meta_mkNoConfusion___closed__8;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_mkNoConfusion___closed__2;
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_41, x_40, x_3, x_4, x_5, x_6, x_35);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
lean_dec(x_37);
if (lean_obj_tag(x_43) == 5)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_45 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Meta_mkNoConfusion___closed__1;
x_51 = l_Lean_Name_str___override(x_49, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_32);
x_53 = l_Lean_Expr_const___override(x_51, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_28, x_54);
x_56 = l_Lean_Meta_mkNoConfusion___closed__9;
lean_inc(x_55);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_57, x_59);
x_61 = l_Lean_Meta_mkNoConfusion___closed__10;
x_62 = lean_array_push(x_61, x_1);
x_63 = lean_array_push(x_62, x_25);
x_64 = lean_array_push(x_63, x_26);
x_65 = lean_array_push(x_64, x_2);
x_66 = l_Array_append___rarg(x_60, x_65);
x_67 = l_Lean_mkAppN(x_53, x_66);
lean_ctor_set(x_45, 0, x_67);
return x_45;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_70 = lean_ctor_get(x_44, 0);
lean_inc(x_70);
lean_dec(x_44);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Lean_Meta_mkNoConfusion___closed__1;
x_73 = l_Lean_Name_str___override(x_71, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_32);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_28, x_76);
x_78 = l_Lean_Meta_mkNoConfusion___closed__9;
lean_inc(x_77);
x_79 = lean_mk_array(x_77, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_77, x_80);
lean_dec(x_77);
x_82 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_79, x_81);
x_83 = l_Lean_Meta_mkNoConfusion___closed__10;
x_84 = lean_array_push(x_83, x_1);
x_85 = lean_array_push(x_84, x_25);
x_86 = lean_array_push(x_85, x_26);
x_87 = lean_array_push(x_86, x_2);
x_88 = l_Array_append___rarg(x_82, x_87);
x_89 = l_Lean_mkAppN(x_75, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_69);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_44);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_45);
if (x_91 == 0)
{
return x_45;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_45, 0);
x_93 = lean_ctor_get(x_45, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_45);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_43);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_95 = l_Lean_indentExpr(x_28);
x_96 = l_Lean_Meta_mkNoConfusion___closed__8;
x_97 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Meta_mkNoConfusion___closed__2;
x_99 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_98, x_97, x_3, x_4, x_5, x_6, x_35);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l_Lean_indentExpr(x_28);
x_101 = l_Lean_Meta_mkNoConfusion___closed__8;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Meta_mkNoConfusion___closed__2;
x_104 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_103, x_102, x_3, x_4, x_5, x_6, x_29);
return x_104;
}
}
else
{
uint8_t x_105; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
uint8_t x_109; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_11);
if (x_109 == 0)
{
return x_11;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
return x_8;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_8, 0);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_8);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkPure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Pure", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPure___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pure", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkPure___closed__2;
x_2 = l_Lean_Meta_mkPure___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lean_Meta_mkNoConfusion___closed__10;
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_9);
x_15 = lean_array_push(x_14, x_10);
x_16 = l_Lean_Meta_mkPure___closed__4;
x_17 = l_Lean_Meta_mkAppOptM(x_16, x_15, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_35; 
lean_dec(x_9);
x_17 = lean_array_uget(x_6, x_8);
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_4);
x_35 = l_Lean_isSubobjectField_x3f(x_4, x_3, x_17);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec(x_17);
x_36 = lean_box(0);
x_18 = x_36;
x_19 = x_14;
goto block_34;
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_39 = l_Lean_Meta_mkProjection(x_1, x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_saveState___rarg(x_11, x_12, x_13, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_45 = l_Lean_Meta_mkProjection(x_40, x_2, x_10, x_11, x_12, x_13, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_ctor_set(x_35, 0, x_46);
x_18 = x_35;
x_19 = x_47;
goto block_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_35);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_SavedState_restore(x_43, x_10, x_11, x_12, x_13, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_18 = x_51;
x_19 = x_50;
goto block_34;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_56 = l_Lean_Meta_mkProjection(x_1, x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_saveState___rarg(x_11, x_12, x_13, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_62 = l_Lean_Meta_mkProjection(x_57, x_2, x_10, x_11, x_12, x_13, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_18 = x_65;
x_19 = x_64;
goto block_34;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = l_Lean_Meta_SavedState_restore(x_60, x_10, x_11, x_12, x_13, x_66);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_box(0);
x_18 = x_69;
x_19 = x_68;
goto block_34;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
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
block_34:
{
if (lean_obj_tag(x_18) == 0)
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_8, x_20);
lean_inc(x_5);
{
size_t _tmp_7 = x_21;
lean_object* _tmp_8 = x_5;
lean_object* _tmp_13 = x_19;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_14 = _tmp_13;
}
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_19);
return x_33;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mkProjectionn", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkProjection___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid field name '", 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' for", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_getProjFnForField_x3f(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_getStructureFields(x_1, x_2);
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_36 = l_Lean_Meta_mkProjection___lambda__1___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_4);
x_37 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1(x_4, x_3, x_2, x_1, x_36, x_14, x_17, x_18, x_36, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_19 = x_15;
x_20 = x_40;
goto block_35;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_19 = x_42;
x_20 = x_41;
goto block_35;
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_35:
{
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = 1;
x_22 = l_Lean_Name_toString(x_3, x_21);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Meta_mkProjection___lambda__1___closed__6;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_mkProjection___lambda__1___closed__9;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_4, x_5);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_mkProjection___lambda__1___closed__3;
x_32 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_31, x_30, x_8, x_9, x_10, x_11, x_20);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_19, 0);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_20);
return x_34;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_48);
x_50 = l_Lean_Meta_mkNoConfusion___closed__9;
lean_inc(x_49);
x_51 = lean_mk_array(x_49, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_5, x_51, x_53);
x_55 = l_Lean_Expr_const___override(x_47, x_6);
x_56 = l_Lean_mkAppN(x_55, x_54);
x_57 = l_Lean_Expr_app___override(x_56, x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
return x_58;
}
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structure expected", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mkProjection", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkProjection___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_whnf(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_getAppFn(x_12);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_st_ref_get(x_6, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_20);
x_21 = l_Lean_isStructure(x_20, x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_2);
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_23 = l_Lean_Meta_mkProjection___closed__3;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_mkProjection___closed__5;
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_25, x_24, x_3, x_4, x_5, x_6, x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_Meta_mkProjection___lambda__1(x_20, x_15, x_2, x_1, x_12, x_16, x_31, x_3, x_4, x_5, x_6, x_19);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
lean_dec(x_2);
x_33 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_34 = l_Lean_Meta_mkProjection___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_mkProjection___lambda__1___closed__3;
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_36, x_35, x_3, x_4, x_5, x_6, x_13);
return x_37;
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
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_8);
if (x_42 == 0)
{
return x_8;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_8, 0);
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_8);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_mkProjection___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
x_6 = l_Lean_Expr_app___override(x_2, x_4);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_5);
x_8 = l_Lean_Expr_app___override(x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("List", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkListLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nil", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkListLit___closed__2;
x_2 = l_Lean_Meta_mkListLit___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cons", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkListLit___closed__2;
x_2 = l_Lean_Meta_mkListLit___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkListLit___closed__4;
lean_inc(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_12);
lean_inc(x_1);
x_15 = l_Lean_Expr_app___override(x_14, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Meta_mkListLit___closed__6;
x_17 = l_Lean_Expr_const___override(x_16, x_12);
x_18 = l_Lean_Expr_app___override(x_17, x_1);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_15, x_18, x_2);
lean_dec(x_15);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_mkListLit___closed__4;
lean_inc(x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_23);
lean_inc(x_1);
x_26 = l_Lean_Expr_app___override(x_25, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; 
lean_dec(x_23);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = l_Lean_Meta_mkListLit___closed__6;
x_29 = l_Lean_Expr_const___override(x_28, x_23);
x_30 = l_Lean_Expr_app___override(x_29, x_1);
x_31 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(x_26, x_30, x_2);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("toArray", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkListLit___closed__2;
x_2 = l_Lean_Meta_mkArrayLit___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Meta_mkListLit(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_mkArrayLit___closed__2;
x_17 = l_Lean_Expr_const___override(x_16, x_15);
x_18 = l_Lean_Expr_app___override(x_17, x_1);
x_19 = l_Lean_Expr_app___override(x_18, x_13);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_mkArrayLit___closed__2;
x_25 = l_Lean_Expr_const___override(x_24, x_23);
x_26 = l_Lean_Expr_app___override(x_25, x_1);
x_27 = l_Lean_Expr_app___override(x_26, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sorryAx", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__4;
x_2 = l_Lean_Meta_mkSorry___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__4;
x_2 = l_Lean_Meta_mkSorry___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkSorry___closed__2;
x_14 = l_Lean_Expr_const___override(x_13, x_12);
if (x_2 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Meta_mkSorry___closed__7;
x_16 = l_Lean_mkAppB(x_14, x_1, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Meta_mkSorry___closed__10;
x_18 = l_Lean_mkAppB(x_14, x_1, x_17);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 0);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_8);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_mkSorry___closed__2;
x_24 = l_Lean_Expr_const___override(x_23, x_22);
if (x_2 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_Meta_mkSorry___closed__7;
x_26 = l_Lean_mkAppB(x_24, x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Meta_mkSorry___closed__10;
x_29 = l_Lean_mkAppB(x_24, x_1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkSorry(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_mkDecide___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Decidable", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecide___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecide___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkDecide___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decide", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecide___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkDecide___closed__2;
x_2 = l_Lean_Meta_mkDecide___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Meta_mkEqMP___closed__3;
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Meta_mkDecide___closed__4;
x_13 = l_Lean_Meta_mkAppOptM(x_12, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("of_decide_eq_true", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecideProof___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_mkDecideProof___closed__1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Meta_mkEq(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkEqRefl(x_10, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkExpectedTypeHint(x_15, x_12, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkDecideProof___closed__4;
x_21 = lean_array_push(x_20, x_18);
x_22 = l_Lean_Meta_mkDecideProof___closed__3;
x_23 = l_Lean_Meta_mkAppM(x_22, x_21, x_2, x_3, x_4, x_5, x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
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
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
static lean_object* _init_l_Lean_Meta_mkLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LT", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLt___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLt___closed__2;
x_2 = l_Lean_Meta_mkLt___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLt___closed__4;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LE", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLe___closed__2;
x_2 = l_Lean_Meta_mkLe___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLe___closed__4;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkDefault___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Inhabited", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDefault___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDefault___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkDefault___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("default", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDefault___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkDefault___closed__2;
x_2 = l_Lean_Meta_mkDefault___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Meta_mkEqMP___closed__3;
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Meta_mkDefault___closed__4;
x_13 = l_Lean_Meta_mkAppOptM(x_12, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_mkOfNonempty___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Classical", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkOfNonempty___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkOfNonempty___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkOfNonempty___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNonempty", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkOfNonempty___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkOfNonempty___closed__2;
x_2 = l_Lean_Meta_mkOfNonempty___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_box(0);
x_9 = l_Lean_Meta_mkEqMP___closed__3;
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Meta_mkOfNonempty___closed__4;
x_13 = l_Lean_Meta_mkAppOptM(x_12, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSyntheticSorry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getLevel(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkSorry___closed__2;
x_13 = l_Lean_Expr_const___override(x_12, x_11);
x_14 = l_Lean_Meta_mkSorry___closed__10;
x_15 = l_Lean_mkAppB(x_13, x_1, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_mkSorry___closed__2;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_Meta_mkSorry___closed__10;
x_23 = l_Lean_mkAppB(x_21, x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkFunExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("funext", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkFunExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkFunExt___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkFunExt___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkPropExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("propext", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPropExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPropExt___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkPropExt___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkLetCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let_congr", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLetCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLetCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLetCongr___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkLetValCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let_val_congr", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLetValCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLetValCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLetValCongr___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkLetBodyCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let_body_congr", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLetBodyCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLetBodyCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLetBodyCongr___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("of_eq_true", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkOfEqTrue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkOfEqTrue___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrue___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEqTrue___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkEqTrue___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkEqFalse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEqFalse___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkEqFalse___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkEqFalse_x27___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false'", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkEqFalse_x27___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEqFalse_x27___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkEqFalse_x27___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkImpCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("implies_congr", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkImpCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkImpCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkImpCongr___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkImpCongrCtx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("implies_congr_ctx", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkImpCongrCtx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkImpCongrCtx___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkImpCongrCtx___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkImpDepCongrCtx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("implies_dep_congr_ctx", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkImpDepCongrCtx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkImpDepCongrCtx___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_mkEqMP___closed__3;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkImpDepCongrCtx___closed__2;
x_12 = l_Lean_Meta_mkAppM(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_mkForallCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forall_congr", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkForallCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkForallCongr___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkForallCongr___closed__2;
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_isMonad_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Monad", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_isMonad_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_isMonad_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_mkDecideProof___closed__4;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_isMonad_x3f___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_mkAppM(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_trySynthInstance(x_11, x_13, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_14, 0);
lean_dec(x_29);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_10, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_34);
return x_10;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkNumeral___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkNumeral___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkNumeral___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkNumeral___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkNumeral___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkNumeral___closed__2;
x_2 = l_Lean_Meta_mkNumeral___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_mkNumeral___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_mkRawNatLit(x_2);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_mkAppB(x_14, x_1, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_synthInstance(x_16, x_17, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_Meta_mkNumeral___closed__4;
x_22 = l_Lean_Expr_const___override(x_21, x_12);
x_23 = l_Lean_mkApp3(x_22, x_1, x_15, x_20);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = l_Lean_Meta_mkNumeral___closed__4;
x_27 = l_Lean_Expr_const___override(x_26, x_12);
x_28 = l_Lean_mkApp3(x_27, x_1, x_15, x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_12);
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
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 0);
x_36 = lean_ctor_get(x_8, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_8);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_13 = l_Lean_Meta_getDecLevel(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_19);
x_20 = l_Lean_Expr_const___override(x_1, x_19);
lean_inc_n(x_11, 3);
x_21 = l_Lean_mkApp3(x_20, x_11, x_11, x_11);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_synthInstance(x_21, x_22, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_Expr_const___override(x_2, x_19);
lean_inc_n(x_11, 2);
x_27 = l_Lean_mkApp6(x_26, x_11, x_11, x_11, x_25, x_3, x_4);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = l_Lean_Expr_const___override(x_2, x_19);
lean_inc_n(x_11, 2);
x_31 = l_Lean_mkApp6(x_30, x_11, x_11, x_11, x_28, x_3, x_4);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_13);
if (x_37 == 0)
{
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_10);
if (x_41 == 0)
{
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_10, 0);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAdd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkAdd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkAdd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hAdd", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAdd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkAdd___closed__2;
x_2 = l_Lean_Meta_mkAdd___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkAdd___closed__2;
x_9 = l_Lean_Meta_mkAdd___closed__4;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSub___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSub___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSub___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hSub", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSub___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSub___closed__2;
x_2 = l_Lean_Meta_mkSub___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkSub___closed__2;
x_9 = l_Lean_Meta_mkSub___closed__4;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("HMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkMul___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkMul___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkMul___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hMul", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkMul___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkMul___closed__2;
x_2 = l_Lean_Meta_mkMul___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkMul___closed__2;
x_9 = l_Lean_Meta_mkMul___closed__4;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_11);
x_13 = l_Lean_Meta_getDecLevel(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_17);
x_18 = l_Lean_Expr_const___override(x_1, x_17);
lean_inc(x_11);
x_19 = l_Lean_Expr_app___override(x_18, x_11);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_synthInstance(x_19, x_20, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Expr_const___override(x_2, x_17);
x_25 = l_Lean_mkApp4(x_24, x_11, x_23, x_3, x_4);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Lean_Expr_const___override(x_2, x_17);
x_29 = l_Lean_mkApp4(x_28, x_11, x_26, x_3, x_4);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
return x_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_10, 0);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_10);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkLe___closed__2;
x_9 = l_Lean_Meta_mkLe___closed__4;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkLt___closed__2;
x_9 = l_Lean_Meta_mkLt___closed__4;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_5792_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_mkAppM___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_mkId___closed__1 = _init_l_Lean_Meta_mkId___closed__1();
lean_mark_persistent(l_Lean_Meta_mkId___closed__1);
l_Lean_Meta_mkId___closed__2 = _init_l_Lean_Meta_mkId___closed__2();
lean_mark_persistent(l_Lean_Meta_mkId___closed__2);
l_Lean_Meta_mkEq___closed__1 = _init_l_Lean_Meta_mkEq___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEq___closed__1);
l_Lean_Meta_mkEq___closed__2 = _init_l_Lean_Meta_mkEq___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEq___closed__2);
l_Lean_Meta_mkHEq___closed__1 = _init_l_Lean_Meta_mkHEq___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEq___closed__1);
l_Lean_Meta_mkHEq___closed__2 = _init_l_Lean_Meta_mkHEq___closed__2();
lean_mark_persistent(l_Lean_Meta_mkHEq___closed__2);
l_Lean_Meta_mkEqRefl___closed__1 = _init_l_Lean_Meta_mkEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__1);
l_Lean_Meta_mkEqRefl___closed__2 = _init_l_Lean_Meta_mkEqRefl___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__2);
l_Lean_Meta_mkHEqRefl___closed__1 = _init_l_Lean_Meta_mkHEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqRefl___closed__1);
l_Lean_Meta_mkAbsurd___closed__1 = _init_l_Lean_Meta_mkAbsurd___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAbsurd___closed__1);
l_Lean_Meta_mkAbsurd___closed__2 = _init_l_Lean_Meta_mkAbsurd___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAbsurd___closed__2);
l_Lean_Meta_mkFalseElim___closed__1 = _init_l_Lean_Meta_mkFalseElim___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFalseElim___closed__1);
l_Lean_Meta_mkFalseElim___closed__2 = _init_l_Lean_Meta_mkFalseElim___closed__2();
lean_mark_persistent(l_Lean_Meta_mkFalseElim___closed__2);
l_Lean_Meta_mkFalseElim___closed__3 = _init_l_Lean_Meta_mkFalseElim___closed__3();
lean_mark_persistent(l_Lean_Meta_mkFalseElim___closed__3);
l_Lean_Meta_mkFalseElim___closed__4 = _init_l_Lean_Meta_mkFalseElim___closed__4();
lean_mark_persistent(l_Lean_Meta_mkFalseElim___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4);
l_Lean_Meta_mkEqSymm___closed__1 = _init_l_Lean_Meta_mkEqSymm___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__1);
l_Lean_Meta_mkEqSymm___closed__2 = _init_l_Lean_Meta_mkEqSymm___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__2);
l_Lean_Meta_mkEqSymm___closed__3 = _init_l_Lean_Meta_mkEqSymm___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__3);
l_Lean_Meta_mkEqSymm___closed__4 = _init_l_Lean_Meta_mkEqSymm___closed__4();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__4);
l_Lean_Meta_mkEqSymm___closed__5 = _init_l_Lean_Meta_mkEqSymm___closed__5();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__5);
l_Lean_Meta_mkEqTrans___closed__1 = _init_l_Lean_Meta_mkEqTrans___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqTrans___closed__1);
l_Lean_Meta_mkEqTrans___closed__2 = _init_l_Lean_Meta_mkEqTrans___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqTrans___closed__2);
l_Lean_Meta_mkHEqSymm___closed__1 = _init_l_Lean_Meta_mkHEqSymm___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__1);
l_Lean_Meta_mkHEqSymm___closed__2 = _init_l_Lean_Meta_mkHEqSymm___closed__2();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__2);
l_Lean_Meta_mkHEqSymm___closed__3 = _init_l_Lean_Meta_mkHEqSymm___closed__3();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__3);
l_Lean_Meta_mkHEqSymm___closed__4 = _init_l_Lean_Meta_mkHEqSymm___closed__4();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__4);
l_Lean_Meta_mkHEqTrans___closed__1 = _init_l_Lean_Meta_mkHEqTrans___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqTrans___closed__1);
l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1 = _init_l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1);
l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2 = _init_l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2);
l_Lean_Meta_mkEqOfHEq___closed__1 = _init_l_Lean_Meta_mkEqOfHEq___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__1);
l_Lean_Meta_mkEqOfHEq___closed__2 = _init_l_Lean_Meta_mkEqOfHEq___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__2);
l_Lean_Meta_mkEqOfHEq___closed__3 = _init_l_Lean_Meta_mkEqOfHEq___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__3);
l_Lean_Meta_mkEqOfHEq___closed__4 = _init_l_Lean_Meta_mkEqOfHEq___closed__4();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__4);
l_Lean_Meta_mkEqOfHEq___closed__5 = _init_l_Lean_Meta_mkEqOfHEq___closed__5();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__5);
l_Lean_Meta_mkCongrArg___closed__1 = _init_l_Lean_Meta_mkCongrArg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__1);
l_Lean_Meta_mkCongrArg___closed__2 = _init_l_Lean_Meta_mkCongrArg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__2);
l_Lean_Meta_mkCongrArg___closed__3 = _init_l_Lean_Meta_mkCongrArg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__3);
l_Lean_Meta_mkCongrArg___closed__4 = _init_l_Lean_Meta_mkCongrArg___closed__4();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__4);
l_Lean_Meta_mkCongrArg___closed__5 = _init_l_Lean_Meta_mkCongrArg___closed__5();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__5);
l_Lean_Meta_mkCongrFun___closed__1 = _init_l_Lean_Meta_mkCongrFun___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__1);
l_Lean_Meta_mkCongrFun___closed__2 = _init_l_Lean_Meta_mkCongrFun___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__2);
l_Lean_Meta_mkCongrFun___closed__3 = _init_l_Lean_Meta_mkCongrFun___closed__3();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__3);
l_Lean_Meta_mkCongrFun___closed__4 = _init_l_Lean_Meta_mkCongrFun___closed__4();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__4);
l_Lean_Meta_mkCongrFun___closed__5 = _init_l_Lean_Meta_mkCongrFun___closed__5();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__5);
l_Lean_Meta_mkCongr___closed__1 = _init_l_Lean_Meta_mkCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongr___closed__1);
l_Lean_Meta_mkCongr___closed__2 = _init_l_Lean_Meta_mkCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongr___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__10);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__11);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__12);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__13);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1);
l_Lean_Meta_mkAppM___lambda__1___closed__1 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__1);
l_Lean_Meta_mkAppM___lambda__1___closed__2 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__2);
l_Lean_Meta_mkAppM___lambda__1___closed__3 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__3);
l_Lean_Meta_mkAppM___lambda__1___closed__4 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__4);
l_Lean_Meta_mkAppM___lambda__1___closed__5 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__5);
l_Lean_Meta_mkAppM___lambda__1___closed__6 = _init_l_Lean_Meta_mkAppM___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_mkAppM___lambda__1___closed__6);
l_Lean_Meta_mkAppM___closed__1 = _init_l_Lean_Meta_mkAppM___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__1);
l_Lean_Meta_mkAppM___closed__2 = _init_l_Lean_Meta_mkAppM___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__2);
l_Lean_Meta_mkAppM___closed__3 = _init_l_Lean_Meta_mkAppM___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__3);
l_Lean_Meta_mkAppM___closed__4 = _init_l_Lean_Meta_mkAppM___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__4);
l_Lean_Meta_mkAppM_x27___lambda__1___closed__1 = _init_l_Lean_Meta_mkAppM_x27___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM_x27___lambda__1___closed__1);
l_Lean_Meta_mkAppM_x27___lambda__1___closed__2 = _init_l_Lean_Meta_mkAppM_x27___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM_x27___lambda__1___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10);
l_Lean_Meta_mkEqNDRec___closed__1 = _init_l_Lean_Meta_mkEqNDRec___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__1);
l_Lean_Meta_mkEqNDRec___closed__2 = _init_l_Lean_Meta_mkEqNDRec___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__2);
l_Lean_Meta_mkEqNDRec___closed__3 = _init_l_Lean_Meta_mkEqNDRec___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__3);
l_Lean_Meta_mkEqNDRec___closed__4 = _init_l_Lean_Meta_mkEqNDRec___closed__4();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__4);
l_Lean_Meta_mkEqNDRec___closed__5 = _init_l_Lean_Meta_mkEqNDRec___closed__5();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__5);
l_Lean_Meta_mkEqNDRec___closed__6 = _init_l_Lean_Meta_mkEqNDRec___closed__6();
lean_mark_persistent(l_Lean_Meta_mkEqNDRec___closed__6);
l_Lean_Meta_mkEqRec___closed__1 = _init_l_Lean_Meta_mkEqRec___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqRec___closed__1);
l_Lean_Meta_mkEqRec___closed__2 = _init_l_Lean_Meta_mkEqRec___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqRec___closed__2);
l_Lean_Meta_mkEqMP___closed__1 = _init_l_Lean_Meta_mkEqMP___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMP___closed__1);
l_Lean_Meta_mkEqMP___closed__2 = _init_l_Lean_Meta_mkEqMP___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMP___closed__2);
l_Lean_Meta_mkEqMP___closed__3 = _init_l_Lean_Meta_mkEqMP___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqMP___closed__3);
l_Lean_Meta_mkEqMPR___closed__1 = _init_l_Lean_Meta_mkEqMPR___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___closed__1);
l_Lean_Meta_mkEqMPR___closed__2 = _init_l_Lean_Meta_mkEqMPR___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMPR___closed__2);
l_Lean_Meta_mkNoConfusion___closed__1 = _init_l_Lean_Meta_mkNoConfusion___closed__1();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__1);
l_Lean_Meta_mkNoConfusion___closed__2 = _init_l_Lean_Meta_mkNoConfusion___closed__2();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__2);
l_Lean_Meta_mkNoConfusion___closed__3 = _init_l_Lean_Meta_mkNoConfusion___closed__3();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__3);
l_Lean_Meta_mkNoConfusion___closed__4 = _init_l_Lean_Meta_mkNoConfusion___closed__4();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__4);
l_Lean_Meta_mkNoConfusion___closed__5 = _init_l_Lean_Meta_mkNoConfusion___closed__5();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__5);
l_Lean_Meta_mkNoConfusion___closed__6 = _init_l_Lean_Meta_mkNoConfusion___closed__6();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__6);
l_Lean_Meta_mkNoConfusion___closed__7 = _init_l_Lean_Meta_mkNoConfusion___closed__7();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__7);
l_Lean_Meta_mkNoConfusion___closed__8 = _init_l_Lean_Meta_mkNoConfusion___closed__8();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__8);
l_Lean_Meta_mkNoConfusion___closed__9 = _init_l_Lean_Meta_mkNoConfusion___closed__9();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__9);
l_Lean_Meta_mkNoConfusion___closed__10 = _init_l_Lean_Meta_mkNoConfusion___closed__10();
lean_mark_persistent(l_Lean_Meta_mkNoConfusion___closed__10);
l_Lean_Meta_mkPure___closed__1 = _init_l_Lean_Meta_mkPure___closed__1();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__1);
l_Lean_Meta_mkPure___closed__2 = _init_l_Lean_Meta_mkPure___closed__2();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__2);
l_Lean_Meta_mkPure___closed__3 = _init_l_Lean_Meta_mkPure___closed__3();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__3);
l_Lean_Meta_mkPure___closed__4 = _init_l_Lean_Meta_mkPure___closed__4();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__4);
l_Lean_Meta_mkProjection___lambda__1___closed__1 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__1);
l_Lean_Meta_mkProjection___lambda__1___closed__2 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__2);
l_Lean_Meta_mkProjection___lambda__1___closed__3 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__3);
l_Lean_Meta_mkProjection___lambda__1___closed__4 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__4);
l_Lean_Meta_mkProjection___lambda__1___closed__5 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__5);
l_Lean_Meta_mkProjection___lambda__1___closed__6 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__6);
l_Lean_Meta_mkProjection___lambda__1___closed__7 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__7);
l_Lean_Meta_mkProjection___lambda__1___closed__8 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__8);
l_Lean_Meta_mkProjection___lambda__1___closed__9 = _init_l_Lean_Meta_mkProjection___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_mkProjection___lambda__1___closed__9);
l_Lean_Meta_mkProjection___closed__1 = _init_l_Lean_Meta_mkProjection___closed__1();
lean_mark_persistent(l_Lean_Meta_mkProjection___closed__1);
l_Lean_Meta_mkProjection___closed__2 = _init_l_Lean_Meta_mkProjection___closed__2();
lean_mark_persistent(l_Lean_Meta_mkProjection___closed__2);
l_Lean_Meta_mkProjection___closed__3 = _init_l_Lean_Meta_mkProjection___closed__3();
lean_mark_persistent(l_Lean_Meta_mkProjection___closed__3);
l_Lean_Meta_mkProjection___closed__4 = _init_l_Lean_Meta_mkProjection___closed__4();
lean_mark_persistent(l_Lean_Meta_mkProjection___closed__4);
l_Lean_Meta_mkProjection___closed__5 = _init_l_Lean_Meta_mkProjection___closed__5();
lean_mark_persistent(l_Lean_Meta_mkProjection___closed__5);
l_Lean_Meta_mkListLit___closed__1 = _init_l_Lean_Meta_mkListLit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__1);
l_Lean_Meta_mkListLit___closed__2 = _init_l_Lean_Meta_mkListLit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__2);
l_Lean_Meta_mkListLit___closed__3 = _init_l_Lean_Meta_mkListLit___closed__3();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__3);
l_Lean_Meta_mkListLit___closed__4 = _init_l_Lean_Meta_mkListLit___closed__4();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__4);
l_Lean_Meta_mkListLit___closed__5 = _init_l_Lean_Meta_mkListLit___closed__5();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__5);
l_Lean_Meta_mkListLit___closed__6 = _init_l_Lean_Meta_mkListLit___closed__6();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__6);
l_Lean_Meta_mkArrayLit___closed__1 = _init_l_Lean_Meta_mkArrayLit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkArrayLit___closed__1);
l_Lean_Meta_mkArrayLit___closed__2 = _init_l_Lean_Meta_mkArrayLit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkArrayLit___closed__2);
l_Lean_Meta_mkSorry___closed__1 = _init_l_Lean_Meta_mkSorry___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__1);
l_Lean_Meta_mkSorry___closed__2 = _init_l_Lean_Meta_mkSorry___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__2);
l_Lean_Meta_mkSorry___closed__3 = _init_l_Lean_Meta_mkSorry___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__3);
l_Lean_Meta_mkSorry___closed__4 = _init_l_Lean_Meta_mkSorry___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__4);
l_Lean_Meta_mkSorry___closed__5 = _init_l_Lean_Meta_mkSorry___closed__5();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__5);
l_Lean_Meta_mkSorry___closed__6 = _init_l_Lean_Meta_mkSorry___closed__6();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__6);
l_Lean_Meta_mkSorry___closed__7 = _init_l_Lean_Meta_mkSorry___closed__7();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__7);
l_Lean_Meta_mkSorry___closed__8 = _init_l_Lean_Meta_mkSorry___closed__8();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__8);
l_Lean_Meta_mkSorry___closed__9 = _init_l_Lean_Meta_mkSorry___closed__9();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__9);
l_Lean_Meta_mkSorry___closed__10 = _init_l_Lean_Meta_mkSorry___closed__10();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__10);
l_Lean_Meta_mkDecide___closed__1 = _init_l_Lean_Meta_mkDecide___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__1);
l_Lean_Meta_mkDecide___closed__2 = _init_l_Lean_Meta_mkDecide___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__2);
l_Lean_Meta_mkDecide___closed__3 = _init_l_Lean_Meta_mkDecide___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__3);
l_Lean_Meta_mkDecide___closed__4 = _init_l_Lean_Meta_mkDecide___closed__4();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__4);
l_Lean_Meta_mkDecideProof___closed__1 = _init_l_Lean_Meta_mkDecideProof___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___closed__1);
l_Lean_Meta_mkDecideProof___closed__2 = _init_l_Lean_Meta_mkDecideProof___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___closed__2);
l_Lean_Meta_mkDecideProof___closed__3 = _init_l_Lean_Meta_mkDecideProof___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___closed__3);
l_Lean_Meta_mkDecideProof___closed__4 = _init_l_Lean_Meta_mkDecideProof___closed__4();
lean_mark_persistent(l_Lean_Meta_mkDecideProof___closed__4);
l_Lean_Meta_mkLt___closed__1 = _init_l_Lean_Meta_mkLt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLt___closed__1);
l_Lean_Meta_mkLt___closed__2 = _init_l_Lean_Meta_mkLt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLt___closed__2);
l_Lean_Meta_mkLt___closed__3 = _init_l_Lean_Meta_mkLt___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLt___closed__3);
l_Lean_Meta_mkLt___closed__4 = _init_l_Lean_Meta_mkLt___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLt___closed__4);
l_Lean_Meta_mkLe___closed__1 = _init_l_Lean_Meta_mkLe___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__1);
l_Lean_Meta_mkLe___closed__2 = _init_l_Lean_Meta_mkLe___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__2);
l_Lean_Meta_mkLe___closed__3 = _init_l_Lean_Meta_mkLe___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__3);
l_Lean_Meta_mkLe___closed__4 = _init_l_Lean_Meta_mkLe___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__4);
l_Lean_Meta_mkDefault___closed__1 = _init_l_Lean_Meta_mkDefault___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__1);
l_Lean_Meta_mkDefault___closed__2 = _init_l_Lean_Meta_mkDefault___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__2);
l_Lean_Meta_mkDefault___closed__3 = _init_l_Lean_Meta_mkDefault___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__3);
l_Lean_Meta_mkDefault___closed__4 = _init_l_Lean_Meta_mkDefault___closed__4();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__4);
l_Lean_Meta_mkOfNonempty___closed__1 = _init_l_Lean_Meta_mkOfNonempty___closed__1();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__1);
l_Lean_Meta_mkOfNonempty___closed__2 = _init_l_Lean_Meta_mkOfNonempty___closed__2();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__2);
l_Lean_Meta_mkOfNonempty___closed__3 = _init_l_Lean_Meta_mkOfNonempty___closed__3();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__3);
l_Lean_Meta_mkOfNonempty___closed__4 = _init_l_Lean_Meta_mkOfNonempty___closed__4();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__4);
l_Lean_Meta_mkFunExt___closed__1 = _init_l_Lean_Meta_mkFunExt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkFunExt___closed__1);
l_Lean_Meta_mkFunExt___closed__2 = _init_l_Lean_Meta_mkFunExt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkFunExt___closed__2);
l_Lean_Meta_mkPropExt___closed__1 = _init_l_Lean_Meta_mkPropExt___closed__1();
lean_mark_persistent(l_Lean_Meta_mkPropExt___closed__1);
l_Lean_Meta_mkPropExt___closed__2 = _init_l_Lean_Meta_mkPropExt___closed__2();
lean_mark_persistent(l_Lean_Meta_mkPropExt___closed__2);
l_Lean_Meta_mkLetCongr___closed__1 = _init_l_Lean_Meta_mkLetCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLetCongr___closed__1);
l_Lean_Meta_mkLetCongr___closed__2 = _init_l_Lean_Meta_mkLetCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLetCongr___closed__2);
l_Lean_Meta_mkLetValCongr___closed__1 = _init_l_Lean_Meta_mkLetValCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLetValCongr___closed__1);
l_Lean_Meta_mkLetValCongr___closed__2 = _init_l_Lean_Meta_mkLetValCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLetValCongr___closed__2);
l_Lean_Meta_mkLetBodyCongr___closed__1 = _init_l_Lean_Meta_mkLetBodyCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLetBodyCongr___closed__1);
l_Lean_Meta_mkLetBodyCongr___closed__2 = _init_l_Lean_Meta_mkLetBodyCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLetBodyCongr___closed__2);
l_Lean_Meta_mkOfEqTrue___closed__1 = _init_l_Lean_Meta_mkOfEqTrue___closed__1();
lean_mark_persistent(l_Lean_Meta_mkOfEqTrue___closed__1);
l_Lean_Meta_mkOfEqTrue___closed__2 = _init_l_Lean_Meta_mkOfEqTrue___closed__2();
lean_mark_persistent(l_Lean_Meta_mkOfEqTrue___closed__2);
l_Lean_Meta_mkEqTrue___closed__1 = _init_l_Lean_Meta_mkEqTrue___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqTrue___closed__1);
l_Lean_Meta_mkEqTrue___closed__2 = _init_l_Lean_Meta_mkEqTrue___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqTrue___closed__2);
l_Lean_Meta_mkEqFalse___closed__1 = _init_l_Lean_Meta_mkEqFalse___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqFalse___closed__1);
l_Lean_Meta_mkEqFalse___closed__2 = _init_l_Lean_Meta_mkEqFalse___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqFalse___closed__2);
l_Lean_Meta_mkEqFalse_x27___closed__1 = _init_l_Lean_Meta_mkEqFalse_x27___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqFalse_x27___closed__1);
l_Lean_Meta_mkEqFalse_x27___closed__2 = _init_l_Lean_Meta_mkEqFalse_x27___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqFalse_x27___closed__2);
l_Lean_Meta_mkImpCongr___closed__1 = _init_l_Lean_Meta_mkImpCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkImpCongr___closed__1);
l_Lean_Meta_mkImpCongr___closed__2 = _init_l_Lean_Meta_mkImpCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkImpCongr___closed__2);
l_Lean_Meta_mkImpCongrCtx___closed__1 = _init_l_Lean_Meta_mkImpCongrCtx___closed__1();
lean_mark_persistent(l_Lean_Meta_mkImpCongrCtx___closed__1);
l_Lean_Meta_mkImpCongrCtx___closed__2 = _init_l_Lean_Meta_mkImpCongrCtx___closed__2();
lean_mark_persistent(l_Lean_Meta_mkImpCongrCtx___closed__2);
l_Lean_Meta_mkImpDepCongrCtx___closed__1 = _init_l_Lean_Meta_mkImpDepCongrCtx___closed__1();
lean_mark_persistent(l_Lean_Meta_mkImpDepCongrCtx___closed__1);
l_Lean_Meta_mkImpDepCongrCtx___closed__2 = _init_l_Lean_Meta_mkImpDepCongrCtx___closed__2();
lean_mark_persistent(l_Lean_Meta_mkImpDepCongrCtx___closed__2);
l_Lean_Meta_mkForallCongr___closed__1 = _init_l_Lean_Meta_mkForallCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkForallCongr___closed__1);
l_Lean_Meta_mkForallCongr___closed__2 = _init_l_Lean_Meta_mkForallCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkForallCongr___closed__2);
l_Lean_Meta_isMonad_x3f___closed__1 = _init_l_Lean_Meta_isMonad_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_isMonad_x3f___closed__1);
l_Lean_Meta_isMonad_x3f___closed__2 = _init_l_Lean_Meta_isMonad_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_isMonad_x3f___closed__2);
l_Lean_Meta_mkNumeral___closed__1 = _init_l_Lean_Meta_mkNumeral___closed__1();
lean_mark_persistent(l_Lean_Meta_mkNumeral___closed__1);
l_Lean_Meta_mkNumeral___closed__2 = _init_l_Lean_Meta_mkNumeral___closed__2();
lean_mark_persistent(l_Lean_Meta_mkNumeral___closed__2);
l_Lean_Meta_mkNumeral___closed__3 = _init_l_Lean_Meta_mkNumeral___closed__3();
lean_mark_persistent(l_Lean_Meta_mkNumeral___closed__3);
l_Lean_Meta_mkNumeral___closed__4 = _init_l_Lean_Meta_mkNumeral___closed__4();
lean_mark_persistent(l_Lean_Meta_mkNumeral___closed__4);
l_Lean_Meta_mkAdd___closed__1 = _init_l_Lean_Meta_mkAdd___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAdd___closed__1);
l_Lean_Meta_mkAdd___closed__2 = _init_l_Lean_Meta_mkAdd___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAdd___closed__2);
l_Lean_Meta_mkAdd___closed__3 = _init_l_Lean_Meta_mkAdd___closed__3();
lean_mark_persistent(l_Lean_Meta_mkAdd___closed__3);
l_Lean_Meta_mkAdd___closed__4 = _init_l_Lean_Meta_mkAdd___closed__4();
lean_mark_persistent(l_Lean_Meta_mkAdd___closed__4);
l_Lean_Meta_mkSub___closed__1 = _init_l_Lean_Meta_mkSub___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSub___closed__1);
l_Lean_Meta_mkSub___closed__2 = _init_l_Lean_Meta_mkSub___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSub___closed__2);
l_Lean_Meta_mkSub___closed__3 = _init_l_Lean_Meta_mkSub___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSub___closed__3);
l_Lean_Meta_mkSub___closed__4 = _init_l_Lean_Meta_mkSub___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSub___closed__4);
l_Lean_Meta_mkMul___closed__1 = _init_l_Lean_Meta_mkMul___closed__1();
lean_mark_persistent(l_Lean_Meta_mkMul___closed__1);
l_Lean_Meta_mkMul___closed__2 = _init_l_Lean_Meta_mkMul___closed__2();
lean_mark_persistent(l_Lean_Meta_mkMul___closed__2);
l_Lean_Meta_mkMul___closed__3 = _init_l_Lean_Meta_mkMul___closed__3();
lean_mark_persistent(l_Lean_Meta_mkMul___closed__3);
l_Lean_Meta_mkMul___closed__4 = _init_l_Lean_Meta_mkMul___closed__4();
lean_mark_persistent(l_Lean_Meta_mkMul___closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_5792_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
