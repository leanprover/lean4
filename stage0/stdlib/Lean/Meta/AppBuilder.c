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
lean_object* l_List_reverse___rarg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8;
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__9;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__1;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongr___closed__1;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqMP___closed__3;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__1;
static lean_object* l_Lean_Meta_mkEqSymm___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_mkDecideProof___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11;
static lean_object* l_Lean_Meta_mkAbsurd___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkImpCongr___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3;
static lean_object* l_Lean_Meta_mkAbsurd___closed__1;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecideProof___closed__2;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3;
static lean_object* l_Lean_Meta_mkPure___closed__2;
lean_object* l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__1;
static lean_object* l_Lean_Meta_mkHEqSymm___closed__4;
static lean_object* l_Lean_Meta_mkCongr___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkPure___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__5;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4;
static lean_object* l_Lean_Meta_mkId___closed__1;
static lean_object* l_Lean_Meta_mkSorry___closed__8;
static lean_object* l_Lean_Meta_mkLE___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__3;
static lean_object* l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__9;
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLetBodyCongr___closed__2;
static lean_object* l_Lean_Meta_mkDecide___closed__1;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__4;
static lean_object* l_Lean_Meta_mkSorry___closed__9;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_mkLetBodyCongr___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4;
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
static lean_object* l_Lean_Meta_mkIffOfEq___closed__1;
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_crossEmoji;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_mkProjection___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__6;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__2;
static lean_object* l_Lean_Meta_mkHEq___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__2;
static lean_object* l_Lean_Meta_mkIffOfEq___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkHEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecide___closed__3;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1(lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__1;
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
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__3;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqNDRec___closed__6;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__2;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__1;
static lean_object* l_Lean_Meta_mkLetValCongr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNumeral___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLetValCongr___closed__1;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__4;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5;
static lean_object* l_Lean_Meta_mkEqRec___closed__2;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkDecideProof___closed__4;
static lean_object* l_Lean_Meta_mkListLit___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4;
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_mkNumeral___closed__1;
static lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqTrans___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12;
static lean_object* l_Lean_Meta_mkDefault___closed__3;
static lean_object* l_Lean_Meta_mkLetCongr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqRec___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_mkEqSymm___closed__5;
static lean_object* l_Lean_Meta_mkForallCongr___closed__2;
static lean_object* l_Lean_Meta_mkEqTrans___closed__2;
static lean_object* l_Lean_Meta_mkEqFalse_x27___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkForallCongr___closed__1;
static lean_object* l_Lean_Meta_mkPropExt___closed__1;
static lean_object* l_Lean_Meta_mkCongrFun___closed__1;
static lean_object* l_Lean_Meta_mkArrayLit___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__1;
static lean_object* l_Lean_Meta_mkMul___closed__2;
static lean_object* l_Lean_Meta_mkCongrFun___closed__2;
static lean_object* l_Lean_Meta_mkEqMPR___closed__2;
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
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14;
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkIffOfEq___closed__3;
static lean_object* l_Lean_Meta_mkCongrFun___closed__4;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__2;
static lean_object* l_Lean_Meta_mkFunExt___closed__2;
static lean_object* l_Lean_Meta_mkSorry___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__3;
static lean_object* l_Lean_Meta_mkEqRefl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrArg___closed__5;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkNoConfusion___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkListLit___closed__3;
static lean_object* l_Lean_Meta_mkListLit___closed__5;
static lean_object* l_Lean_Meta_mkEqNDRec___closed__2;
static lean_object* l_Lean_Meta_mkEqTrue___closed__1;
static lean_object* l_Lean_Meta_mkEqSymm___closed__4;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_checkEmoji;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__6;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isMonad_x3f___closed__1;
static lean_object* l_Lean_Meta_mkMul___closed__1;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__10;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkSyntheticSorry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1;
static lean_object* l_Lean_Meta_mkSorry___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__3;
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__9;
static lean_object* l_Lean_Meta_mkEqMPR___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114_(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLt___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__3;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
static lean_object* l_Lean_Meta_mkImpDepCongrCtx___closed__1;
static lean_object* l_Lean_Meta_mkDecideProof___closed__3;
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2;
static lean_object* l_Lean_Meta_isMonad_x3f___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSub___closed__4;
static lean_object* l_Lean_Meta_mkEq___closed__2;
static lean_object* l_Lean_Meta_mkSorry___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__4;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__10;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg___closed__4;
lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkEq___closed__1;
static lean_object* l_Lean_Meta_mkEqOfHEq___closed__5;
static lean_object* l_Lean_Meta_mkSorry___closed__5;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_mkAdd___closed__4;
static lean_object* l_Lean_Meta_mkLt___closed__3;
static lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___closed__1;
static lean_object* l_Lean_Meta_mkHEqTrans___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13;
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkMul___closed__3;
static lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLT___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Meta_mkLe___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6;
static lean_object* l_Lean_Meta_mkImpCongr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrFun___closed__5;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__7;
static lean_object* l_Lean_Meta_mkSorry___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkProjection___closed__2;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkOfEqTrue___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7;
static lean_object* l_Lean_Meta_mkListLit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkCongrFun___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__4;
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkHEq___closed__1;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elim", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkFalseElim___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkFalseElim___closed__1;
x_2 = l_Lean_Meta_mkFalseElim___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_13 = l_Lean_Meta_mkFalseElim___closed__3;
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
x_20 = l_Lean_Meta_mkFalseElim___closed__3;
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_mkEq___closed__2;
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Expr_isAppOfArity(x_12, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_2);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_21 = l_Lean_Meta_mkEqSymm___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_mkEqTrans___closed__2;
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_23, x_22, x_3, x_4, x_5, x_6, x_16);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isAppOfArity(x_15, x_17, x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_1);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_27 = l_Lean_Meta_mkEqSymm___closed__5;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_mkEqTrans___closed__2;
x_30 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_29, x_28, x_3, x_4, x_5, x_6, x_16);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Lean_Expr_appFn_x21(x_12);
x_32 = l_Lean_Expr_appFn_x21(x_31);
x_33 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_34 = l_Lean_Expr_appArg_x21(x_31);
lean_dec(x_31);
x_35 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_36 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
lean_inc(x_33);
x_37 = l_Lean_Meta_getLevel(x_33, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_mkEqTrans___closed__2;
x_43 = l_Lean_Expr_const___override(x_42, x_41);
x_44 = l_Lean_mkApp6(x_43, x_33, x_34, x_35, x_36, x_1, x_2);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_mkEqTrans___closed__2;
x_50 = l_Lean_Expr_const___override(x_49, x_48);
x_51 = l_Lean_mkApp6(x_50, x_33, x_34, x_35, x_36, x_1, x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
return x_14;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_11);
if (x_61 == 0)
{
return x_11;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_11, 0);
x_63 = lean_ctor_get(x_11, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_11);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_7);
return x_66;
}
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkHEq___closed__1;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkHEq___closed__1;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_56 = l_Lean_Meta_mkHEq___closed__2;
x_57 = lean_unsigned_to_nat(4u);
x_58 = l_Lean_Expr_isAppOfArity(x_12, x_56, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_15);
lean_dec(x_2);
x_59 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_60 = l_Lean_Meta_mkHEqSymm___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_mkHEqTrans___closed__1;
x_63 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_62, x_61, x_3, x_4, x_5, x_6, x_16);
return x_63;
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_64 = l_Lean_Expr_isAppOfArity(x_15, x_56, x_57);
x_65 = l_Lean_Expr_appFn_x21(x_12);
x_66 = l_Lean_Expr_appFn_x21(x_65);
x_67 = l_Lean_Expr_appFn_x21(x_66);
x_68 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_66);
lean_dec(x_66);
x_70 = l_Lean_Expr_appArg_x21(x_65);
lean_dec(x_65);
x_71 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
if (x_64 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_17 = x_75;
x_18 = x_74;
goto block_55;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = l_Lean_Expr_appFn_x21(x_15);
x_77 = l_Lean_Expr_appFn_x21(x_76);
x_78 = l_Lean_Expr_appFn_x21(x_77);
x_79 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_80 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
x_81 = l_Lean_Expr_appArg_x21(x_76);
lean_dec(x_76);
x_82 = l_Lean_Expr_appArg_x21(x_15);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_79);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_17 = x_86;
x_18 = x_74;
goto block_55;
}
}
block_55:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_1);
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_22 = l_Lean_Meta_mkHEqSymm___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_mkHEqTrans___closed__1;
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_24, x_23, x_3, x_4, x_5, x_6, x_16);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 1);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_29);
x_35 = l_Lean_Meta_getLevel(x_29, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_mkHEqTrans___closed__1;
x_41 = l_Lean_Expr_const___override(x_40, x_39);
x_42 = l_Lean_mkApp8(x_41, x_29, x_31, x_33, x_30, x_32, x_34, x_1, x_2);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_mkHEqTrans___closed__1;
x_48 = l_Lean_Expr_const___override(x_47, x_46);
x_49 = l_Lean_mkApp8(x_48, x_29, x_31, x_33, x_30, x_32, x_34, x_1, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_14);
if (x_87 == 0)
{
return x_14;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_14, 0);
x_89 = lean_ctor_get(x_14, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_11);
if (x_91 == 0)
{
return x_11;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_11, 0);
x_93 = lean_ctor_get(x_11, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_11);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_7);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_7);
return x_96;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_59; lean_object* x_68; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_93 = l_Lean_Meta_mkEq___closed__2;
x_94 = lean_unsigned_to_nat(3u);
x_95 = l_Lean_Expr_isAppOfArity(x_11, x_93, x_94);
if (lean_obj_tag(x_14) == 7)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_14, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_14, 2);
lean_inc(x_97);
x_98 = l_Lean_Expr_hasLooseBVars(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
if (x_95 == 0)
{
x_59 = x_100;
goto block_67;
}
else
{
x_68 = x_100;
goto block_92;
}
}
else
{
lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_96);
x_101 = lean_box(0);
if (x_95 == 0)
{
x_59 = x_101;
goto block_67;
}
else
{
x_68 = x_101;
goto block_92;
}
}
}
else
{
lean_object* x_102; 
x_102 = lean_box(0);
if (x_95 == 0)
{
x_59 = x_102;
goto block_67;
}
else
{
x_68 = x_102;
goto block_92;
}
}
block_58:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_1);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_11);
x_19 = l_Lean_Meta_mkEqSymm___closed__5;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_mkCongrArg___closed__2;
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_21, x_20, x_3, x_4, x_5, x_6, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_25);
x_29 = l_Lean_Meta_getLevel(x_25, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_26);
x_32 = l_Lean_Meta_getLevel(x_26, x_3, x_4, x_5, x_6, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_mkCongrArg___closed__2;
x_39 = l_Lean_Expr_const___override(x_38, x_37);
x_40 = l_Lean_mkApp6(x_39, x_25, x_26, x_27, x_28, x_1, x_2);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_mkCongrArg___closed__2;
x_47 = l_Lean_Expr_const___override(x_46, x_45);
x_48 = l_Lean_mkApp6(x_47, x_25, x_26, x_27, x_28, x_1, x_2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
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
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
block_67:
{
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_2);
x_60 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_61 = l_Lean_Meta_mkCongrArg___closed__5;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Meta_mkCongrArg___closed__2;
x_64 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_63, x_62, x_3, x_4, x_5, x_6, x_15);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_14);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
lean_dec(x_59);
x_66 = lean_box(0);
x_16 = x_66;
x_17 = x_65;
goto block_58;
}
}
block_92:
{
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_2);
x_69 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_14);
x_70 = l_Lean_Meta_mkCongrArg___closed__5;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Meta_mkCongrArg___closed__2;
x_73 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_72, x_71, x_3, x_4, x_5, x_6, x_15);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_14);
x_74 = !lean_is_exclusive(x_68);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = l_Lean_Expr_appFn_x21(x_11);
x_77 = l_Lean_Expr_appFn_x21(x_76);
x_78 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
x_79 = l_Lean_Expr_appArg_x21(x_76);
lean_dec(x_76);
x_80 = l_Lean_Expr_appArg_x21(x_11);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_68, 0, x_82);
x_16 = x_68;
x_17 = x_75;
goto block_58;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_68, 0);
lean_inc(x_83);
lean_dec(x_68);
x_84 = l_Lean_Expr_appFn_x21(x_11);
x_85 = l_Lean_Expr_appFn_x21(x_84);
x_86 = l_Lean_Expr_appArg_x21(x_85);
lean_dec(x_85);
x_87 = l_Lean_Expr_appArg_x21(x_84);
lean_dec(x_84);
x_88 = l_Lean_Expr_appArg_x21(x_11);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_16 = x_91;
x_17 = x_83;
goto block_58;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_13);
if (x_103 == 0)
{
return x_13;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_13, 0);
x_105 = lean_ctor_get(x_13, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_13);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_10);
if (x_107 == 0)
{
return x_10;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_10, 0);
x_109 = lean_ctor_get(x_10, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_10);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_112 = l_Lean_Expr_app___override(x_1, x_111);
x_113 = l_Lean_Meta_mkEqRefl(x_112, x_3, x_4, x_5, x_6, x_7);
return x_113;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_81 = l_Lean_Meta_mkEq___closed__2;
x_82 = lean_unsigned_to_nat(3u);
x_83 = l_Lean_Expr_isAppOfArity(x_12, x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_15);
lean_dec(x_2);
x_84 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_85 = l_Lean_Meta_mkEqSymm___closed__5;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Meta_mkCongr___closed__2;
x_88 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_87, x_86, x_3, x_4, x_5, x_6, x_16);
return x_88;
}
else
{
uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = l_Lean_Expr_isAppOfArity(x_15, x_81, x_82);
x_90 = l_Lean_Expr_appFn_x21(x_12);
x_91 = l_Lean_Expr_appFn_x21(x_90);
x_92 = l_Lean_Expr_appArg_x21(x_91);
lean_dec(x_91);
x_93 = l_Lean_Expr_appArg_x21(x_90);
lean_dec(x_90);
x_94 = l_Lean_Expr_appArg_x21(x_12);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
if (x_89 == 0)
{
lean_object* x_97; 
x_97 = lean_box(0);
x_17 = x_97;
x_18 = x_96;
goto block_80;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = l_Lean_Expr_appFn_x21(x_15);
x_99 = l_Lean_Expr_appFn_x21(x_98);
x_100 = l_Lean_Expr_appArg_x21(x_99);
lean_dec(x_99);
x_101 = l_Lean_Expr_appArg_x21(x_98);
lean_dec(x_98);
x_102 = l_Lean_Expr_appArg_x21(x_15);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_17 = x_105;
x_18 = x_96;
goto block_80;
}
}
block_80:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_2, x_15);
x_21 = l_Lean_Meta_mkEqSymm___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_mkCongr___closed__2;
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_23, x_22, x_3, x_4, x_5, x_6, x_16);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_33 = l_Lean_Meta_whnfD(x_27, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 7)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_34, 2);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l_Lean_Expr_hasLooseBVars(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_30);
x_45 = l_Lean_Meta_getLevel(x_30, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_43);
x_48 = l_Lean_Meta_getLevel(x_43, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_mkCongr___closed__2;
x_55 = l_Lean_Expr_const___override(x_54, x_53);
x_56 = l_Lean_mkApp8(x_55, x_30, x_43, x_28, x_29, x_31, x_32, x_1, x_2);
lean_ctor_set(x_48, 0, x_56);
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_48, 0);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_48);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_mkCongr___closed__2;
x_63 = l_Lean_Expr_const___override(x_62, x_61);
x_64 = l_Lean_mkApp8(x_63, x_30, x_43, x_28, x_29, x_31, x_32, x_1, x_2);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
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
uint8_t x_70; 
lean_dec(x_43);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_45);
if (x_70 == 0)
{
return x_45;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_45, 0);
x_72 = lean_ctor_get(x_45, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_45);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_43);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_74 = lean_box(0);
x_36 = x_74;
goto block_42;
}
}
else
{
lean_object* x_75; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_75 = lean_box(0);
x_36 = x_75;
goto block_42;
}
block_42:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
x_37 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(x_1, x_12);
x_38 = l_Lean_Meta_mkCongrArg___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_mkCongr___closed__2;
x_41 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_40, x_39, x_3, x_4, x_5, x_6, x_35);
return x_41;
}
}
else
{
uint8_t x_76; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_33);
if (x_76 == 0)
{
return x_33;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_33, 0);
x_78 = lean_ctor_get(x_33, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_33);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_14);
if (x_106 == 0)
{
return x_14;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_14, 0);
x_108 = lean_ctor_get(x_14, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_14);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_11);
if (x_110 == 0)
{
return x_11;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_11, 0);
x_112 = lean_ctor_get(x_11, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_11);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_115 = l_Lean_Meta_mkCongrFun(x_1, x_114, x_3, x_4, x_5, x_6, x_7);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_117 = l_Lean_Meta_mkCongrArg(x_116, x_2, x_3, x_4, x_5, x_6, x_7);
return x_117;
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
x_12 = l_Lean_MVarId_getDecl(x_11, x_5, x_6, x_7, x_8, x_9);
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
x_20 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_11, x_18, x_5, x_6, x_7, x_8, x_19);
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
x_12 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_11, x_5, x_6, x_7, x_8, x_10);
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
x_15 = l_Lean_hasAssignableMVar___at_Lean_Meta_SynthInstance_tryResolve___spec__1(x_13, x_5, x_6, x_7, x_8, x_14);
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
case 0:
{
uint8_t x_22; 
lean_dec(x_15);
x_22 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_24);
x_25 = lean_infer_type(x_24, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_isExprDefEq(x_20, x_26, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_mkAppN(x_1, x_6);
x_33 = l_Lean_Meta_throwAppTypeMismatch___rarg(x_32, x_24, x_8, x_9, x_10, x_11, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_array_push(x_6, x_24);
x_3 = x_17;
x_4 = x_36;
x_6 = x_37;
x_12 = x_34;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_24);
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
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
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
lean_dec(x_24);
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
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
return x_25;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_array_fget(x_2, x_4);
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
}
case 3:
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_13);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_20);
x_71 = 1;
lean_inc(x_8);
x_72 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_70, x_71, x_15, x_8, x_9, x_10, x_11, x_12);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_73);
x_75 = lean_array_push(x_6, x_73);
x_76 = l_Lean_Expr_mvarId_x21(x_73);
x_77 = lean_array_push(x_7, x_76);
x_3 = x_17;
x_6 = x_75;
x_7 = x_77;
x_12 = x_74;
goto _start;
}
default: 
{
lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_21);
lean_dec(x_13);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_20);
x_80 = 0;
lean_inc(x_8);
x_81 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_79, x_80, x_15, x_8, x_9, x_10, x_11, x_12);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_array_push(x_6, x_82);
x_3 = x_17;
x_6 = x_84;
x_12 = x_83;
goto _start;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_13);
x_86 = lean_array_get_size(x_6);
x_87 = lean_expr_instantiate_rev_range(x_3, x_5, x_86, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_88 = l_Lean_Meta_whnfD(x_87, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_isForall(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_92 = l_Lean_indentExpr(x_1);
x_93 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__6;
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__9;
x_99 = l_Lean_MessageData_arrayExpr_toMessageData(x_2, x_97, x_98);
x_100 = l_Lean_indentD(x_99);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
x_105 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___rarg(x_104, x_103, x_8, x_9, x_10, x_11, x_90);
return x_105;
}
else
{
x_3 = x_89;
x_5 = x_86;
x_12 = x_90;
goto _start;
}
}
else
{
uint8_t x_107; 
lean_dec(x_86);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_88);
if (x_107 == 0)
{
return x_88;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_88, 0);
x_109 = lean_ctor_get(x_88, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_88);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2;
x_112 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(x_111, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_112;
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
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_reverse___rarg(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_14);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_6 = x_15;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_2);
x_1 = x_17;
x_2 = x_21;
x_7 = x_20;
goto _start;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_levelParams(x_8);
x_11 = lean_box(0);
x_12 = l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Expr_const___override(x_1, x_13);
x_16 = l_Lean_Core_instantiateTypeLevelParams(x_8, x_13, x_4, x_5, x_14);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_mapM_loop___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_processPostponed___spec__2___rarg(x_8, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = lean_apply_5(x_3, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_23);
x_24 = lean_apply_6(x_2, x_23, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
x_27 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_25, x_4, x_5, x_6, x_7, x_8, x_26);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2(x_23, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_23);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_dec(x_20);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_36);
x_37 = lean_apply_6(x_2, x_36, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_7);
x_40 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_processPostponed___spec__3(x_18, x_1, x_16, x_38, x_4, x_5, x_6, x_7, x_8, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2(x_36, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_36);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" f: ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", xs: ", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_crossEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_checkEmoji;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_1(x_1, x_2);
x_12 = lean_apply_1(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
x_23 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_12);
x_26 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("appBuilder", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("error", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2;
x_3 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("result", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2;
x_3 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_25; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6;
x_29 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_28, x_2, x_3, x_4, x_5, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
lean_ctor_set(x_29, 0, x_26);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
lean_inc(x_26);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_26);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_28, x_37, x_2, x_3, x_4, x_5, x_36);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_26);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_26);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_25, 1);
lean_inc(x_44);
lean_dec(x_25);
x_7 = x_43;
x_8 = x_44;
goto block_24;
}
block_24:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4;
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_2, x_3, x_4, x_5, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_7);
x_18 = l_Lean_Exception_toMessageData(x_7);
x_19 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_9, x_18, x_2, x_3, x_4, x_5, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_7);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___boxed), 10, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_4);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3), 6, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_14 = 1;
x_15 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_13, x_11, x_12, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MonadExcept_ofExcept___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_array_to_list(lean_box(0), x_2);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_10, x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_12 = 1;
x_13 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
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
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lambda__1___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkAppM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_array_to_list(lean_box(0), x_2);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_10, x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_12 = 1;
x_13 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg), 6, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppM_x27___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<not-available>", 15);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3;
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_18);
{
lean_object* _tmp_0 = x_15;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
x_1 = x_20;
x_2 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_array_to_list(lean_box(0), x_2);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2(x_10, x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_12 = 1;
x_13 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lambda__1___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg), 6, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1(x_1, x_2, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_array_to_list(lean_box(0), x_2);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2(x_10, x_11);
x_13 = l_Lean_MessageData_ofList(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
x_16 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
x_19 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
x_24 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_8);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3), 6, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_12 = 1;
x_13 = l_Lean_withTraceNode___at___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___spec__1(x_11, x_9, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
lean_closure_set(x_13, 6, x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenK___spec__1___rarg), 6, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at_Lean_Meta_mkAppOptM_x27___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqNDRec___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqRec___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqMP___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkEq___closed__1;
x_2 = l_Lean_Meta_mkEqMPR___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pure", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkPure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkPure___closed__1;
x_2 = l_Lean_Meta_mkPure___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_16 = l_Lean_Meta_mkPure___closed__3;
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
lean_dec(x_43);
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
lean_dec(x_60);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("nil", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkListLit___closed__1;
x_2 = l_Lean_Meta_mkListLit___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cons", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkListLit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkListLit___closed__1;
x_2 = l_Lean_Meta_mkListLit___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_13 = l_Lean_Meta_mkListLit___closed__3;
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
x_16 = l_Lean_Meta_mkListLit___closed__5;
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
x_24 = l_Lean_Meta_mkListLit___closed__3;
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
x_28 = l_Lean_Meta_mkListLit___closed__5;
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
x_1 = l_Lean_Meta_mkListLit___closed__1;
x_2 = l_Lean_Meta_mkArrayLit___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__3;
x_2 = l_Lean_Meta_mkSorry___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__3;
x_2 = l_Lean_Meta_mkSorry___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__8;
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
x_15 = l_Lean_Meta_mkSorry___closed__6;
x_16 = l_Lean_mkAppB(x_14, x_1, x_15);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Meta_mkSorry___closed__9;
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
x_25 = l_Lean_Meta_mkSorry___closed__6;
x_26 = l_Lean_mkAppB(x_24, x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lean_Meta_mkSorry___closed__9;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("decide", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDecide___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkDecide___closed__1;
x_2 = l_Lean_Meta_mkDecide___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_12 = l_Lean_Meta_mkDecide___closed__3;
x_13 = l_Lean_Meta_mkAppOptM(x_12, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__8;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLt___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLt___closed__1;
x_2 = l_Lean_Meta_mkLt___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_11 = l_Lean_Meta_mkLt___closed__3;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("le", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLe___closed__1;
x_2 = l_Lean_Meta_mkLe___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_11 = l_Lean_Meta_mkLe___closed__3;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("default", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkDefault___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkDefault___closed__1;
x_2 = l_Lean_Meta_mkDefault___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_12 = l_Lean_Meta_mkDefault___closed__3;
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNonempty", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkOfNonempty___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkOfNonempty___closed__1;
x_2 = l_Lean_Meta_mkOfNonempty___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_12 = l_Lean_Meta_mkOfNonempty___closed__3;
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
x_14 = l_Lean_Meta_mkSorry___closed__9;
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
x_22 = l_Lean_Meta_mkSorry___closed__9;
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
x_1 = l_Lean_Meta_mkNumeral___closed__1;
x_2 = l_Lean_Meta_mkNumeral___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkAdd___closed__1;
x_2 = l_Lean_Meta_mkAdd___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkSub___closed__1;
x_2 = l_Lean_Meta_mkSub___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
x_1 = l_Lean_Meta_mkMul___closed__1;
x_2 = l_Lean_Meta_mkMul___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
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
static lean_object* _init_l_Lean_Meta_mkLE___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLe___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkLE___closed__1;
x_9 = l_Lean_Meta_mkLe___closed__3;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkLT___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLt___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_mkLT___closed__1;
x_9 = l_Lean_Meta_mkLt___closed__3;
x_10 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_mkIffOfEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Iff", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkIffOfEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("of_eq", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkIffOfEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkIffOfEq___closed__1;
x_2 = l_Lean_Meta_mkIffOfEq___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_mkPropExt___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_mkDecideProof___closed__4;
x_11 = lean_array_push(x_10, x_1);
x_12 = l_Lean_Meta_mkIffOfEq___closed__3;
x_13 = l_Lean_Meta_mkAppM(x_12, x_11, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8;
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("AppBuilder", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13;
x_2 = lean_unsigned_to_nat(7114u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1;
x_3 = 0;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6;
x_8 = 1;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
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
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__7);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__8);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__9);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__1___closed__10);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__1);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__2);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__3);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__4);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__5);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___lambda__3___closed__6);
l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1 = _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___rarg___closed__1);
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
l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1 = _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__1);
l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2 = _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__2);
l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3 = _init_l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Meta_mkAppOptM___spec__2___closed__3);
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
l_Lean_Meta_mkDecide___closed__1 = _init_l_Lean_Meta_mkDecide___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__1);
l_Lean_Meta_mkDecide___closed__2 = _init_l_Lean_Meta_mkDecide___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__2);
l_Lean_Meta_mkDecide___closed__3 = _init_l_Lean_Meta_mkDecide___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDecide___closed__3);
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
l_Lean_Meta_mkLe___closed__1 = _init_l_Lean_Meta_mkLe___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__1);
l_Lean_Meta_mkLe___closed__2 = _init_l_Lean_Meta_mkLe___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__2);
l_Lean_Meta_mkLe___closed__3 = _init_l_Lean_Meta_mkLe___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLe___closed__3);
l_Lean_Meta_mkDefault___closed__1 = _init_l_Lean_Meta_mkDefault___closed__1();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__1);
l_Lean_Meta_mkDefault___closed__2 = _init_l_Lean_Meta_mkDefault___closed__2();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__2);
l_Lean_Meta_mkDefault___closed__3 = _init_l_Lean_Meta_mkDefault___closed__3();
lean_mark_persistent(l_Lean_Meta_mkDefault___closed__3);
l_Lean_Meta_mkOfNonempty___closed__1 = _init_l_Lean_Meta_mkOfNonempty___closed__1();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__1);
l_Lean_Meta_mkOfNonempty___closed__2 = _init_l_Lean_Meta_mkOfNonempty___closed__2();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__2);
l_Lean_Meta_mkOfNonempty___closed__3 = _init_l_Lean_Meta_mkOfNonempty___closed__3();
lean_mark_persistent(l_Lean_Meta_mkOfNonempty___closed__3);
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
l_Lean_Meta_mkLE___closed__1 = _init_l_Lean_Meta_mkLE___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLE___closed__1);
l_Lean_Meta_mkLT___closed__1 = _init_l_Lean_Meta_mkLT___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLT___closed__1);
l_Lean_Meta_mkIffOfEq___closed__1 = _init_l_Lean_Meta_mkIffOfEq___closed__1();
lean_mark_persistent(l_Lean_Meta_mkIffOfEq___closed__1);
l_Lean_Meta_mkIffOfEq___closed__2 = _init_l_Lean_Meta_mkIffOfEq___closed__2();
lean_mark_persistent(l_Lean_Meta_mkIffOfEq___closed__2);
l_Lean_Meta_mkIffOfEq___closed__3 = _init_l_Lean_Meta_mkIffOfEq___closed__3();
lean_mark_persistent(l_Lean_Meta_mkIffOfEq___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114____closed__14);
res = l_Lean_Meta_initFn____x40_Lean_Meta_AppBuilder___hyg_7114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
