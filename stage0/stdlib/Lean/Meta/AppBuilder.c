// Lean compiler output
// Module: Lean.Meta.AppBuilder
// Imports: Init Lean.Structure Lean.Util.Recognizers Lean.Meta.SynthInstance
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
extern lean_object* l_Lean_Name_toString___closed__1;
extern lean_object* l_Lean_getStructureCtor___closed__2;
lean_object* l_Lean_Meta_mkLt___closed__4;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5;
lean_object* l_Lean_Meta_mkCongr___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___closed__1;
lean_object* l_Lean_Meta_mkEqSymm___closed__1;
lean_object* l_Lean_Meta_mkLe___closed__4;
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Meta_mkDecideProof___closed__1;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3;
lean_object* l_Lean_Meta_mkProjection___main___closed__6;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___closed__2;
lean_object* l_Lean_Meta_mkPure___closed__2;
lean_object* l_Lean_Meta_mkHEqSymm___closed__4;
lean_object* l_Lean_Meta_mkCongr___closed__2;
lean_object* l_Lean_Meta_mkPure___closed__4;
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___closed__4;
lean_object* l_Lean_Meta_mkEqOfHEq___closed__4;
lean_object* l_Lean_Meta_mkPure___closed__1;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6;
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_dec___main(lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId___closed__2;
lean_object* l_Lean_Meta_mkEqOfHEq___closed__8;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__infer(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4;
lean_object* l_Lean_Meta_mkLe(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___closed__5;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_mkId___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8;
lean_object* l_Lean_getProjFnForField_x3f(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_listToExpr___rarg___closed__4;
lean_object* l_Lean_Meta_mkCongrArg___closed__2;
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__4;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5;
lean_object* l_Lean_Meta_mkPure___closed__3;
lean_object* l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__68;
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__3;
lean_object* l_Lean_Meta_mkProjection___main___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3;
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__1;
lean_object* l_Lean_Meta_mkProjection___main___closed__8;
lean_object* l_Lean_Meta_mkEqSymm___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMP___closed__1;
lean_object* l_Lean_Meta_mkEqMP___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main___closed__4;
lean_object* l_Lean_Meta_mkNoConfusion___closed__3;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__3;
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Meta_mkEqNDRec___closed__6;
lean_object* l_Lean_Meta_mkNoConfusion___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6;
lean_object* l_Lean_Meta_mkProjection___main___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion___closed__2;
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4;
lean_object* l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion___closed__8;
lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof___closed__4;
lean_object* l_Lean_Meta_mkListLit___closed__2;
extern lean_object* l_Lean_MessageData_coeOfArrayExpr___closed__2;
lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___closed__1;
lean_object* l_Lean_Meta_mkEqRec___closed__1;
extern lean_object* l_Lean_mkDecIsTrue___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkListLit___closed__1;
lean_object* l_Lean_Meta_mkLe___closed__3;
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___closed__5;
lean_object* l_Lean_Meta_mkEqTrans___closed__2;
lean_object* l_Lean_Meta_mkCongrFun___closed__1;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___closed__2;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__2;
lean_object* l_Lean_Meta_mkEqMPR___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___closed__4;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___closed__1;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrayLit___closed__1;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_mkPure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__4;
lean_object* l_Lean_Meta_mkEqOfHEq___closed__2;
lean_object* l_Lean_Meta_mkEqRefl___closed__2;
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__6;
lean_object* l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__5;
lean_object* l_Lean_Meta_mkEqNDRec___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion___closed__5;
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7;
lean_object* l___private_Lean_Meta_AppBuilder_5__mkFun(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___closed__4;
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion___closed__6;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___closed__1;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__5;
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1;
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkFun___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq___closed__7;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1;
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_mkLt___closed__1;
lean_object* l_Lean_Meta_mkSorry___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5;
lean_object* l_Lean_Meta_mkEqOfHEq___closed__3;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt___closed__2;
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__12;
lean_object* l_Lean_Meta_mkDecideProof___closed__3;
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1;
lean_object* l_Lean_Meta_mkProjection___main___closed__7;
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq___closed__5;
lean_object* l_Lean_Meta_mkLt___closed__3;
lean_object* l_Lean_Meta_mkHEqTrans___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main___closed__10;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkLe___closed__2;
extern lean_object* l___private_Lean_Meta_Basic_12__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_mkListLit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main___closed__5;
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__5;
lean_object* l_Lean_Meta_mkNoConfusion___closed__7;
lean_object* l_Lean_Meta_mkSorry___closed__2;
lean_object* l_Lean_Meta_mkLe___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__3;
extern lean_object* l_Lean_listToExpr___rarg___closed__6;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___main___closed__3;
lean_object* _init_l_Lean_Meta_mkId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("id");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkId___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkId___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkId(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_Meta_getLevel(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkId___closed__2;
x_13 = l_Lean_mkConst(x_12, x_11);
x_14 = l_Lean_mkAppB(x_13, x_5, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkId___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppB(x_20, x_5, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_Meta_getLevel(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_mkId___closed__2;
x_11 = l_Lean_mkConst(x_10, x_9);
x_12 = l_Lean_mkAppB(x_11, x_2, x_1);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_mkId___closed__2;
x_18 = l_Lean_mkConst(x_17, x_16);
x_19 = l_Lean_mkAppB(x_18, x_2, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_mkEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = l_Lean_Meta_getLevel(x_6, x_3, x_7);
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
x_13 = l_Lean_Expr_eq_x3f___closed__2;
x_14 = l_Lean_mkConst(x_13, x_12);
x_15 = l_Lean_mkApp3(x_14, x_6, x_1, x_2);
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
x_20 = l_Lean_Expr_eq_x3f___closed__2;
x_21 = l_Lean_mkConst(x_20, x_19);
x_22 = l_Lean_mkApp3(x_21, x_6, x_1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
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
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_mkHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
x_11 = l_Lean_Meta_getLevel(x_6, x_3, x_10);
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
x_16 = l_Lean_Expr_heq_x3f___closed__2;
x_17 = l_Lean_mkConst(x_16, x_15);
x_18 = l_Lean_mkApp4(x_17, x_6, x_1, x_9, x_2);
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
x_23 = l_Lean_Expr_heq_x3f___closed__2;
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = l_Lean_mkApp4(x_24, x_6, x_1, x_9, x_2);
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
lean_dec(x_6);
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
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
return x_5;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkEqRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_Meta_getLevel(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkEqRefl___closed__2;
x_13 = l_Lean_mkConst(x_12, x_11);
x_14 = l_Lean_mkAppB(x_13, x_5, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkEqRefl___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppB(x_20, x_5, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqRefl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkHEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_Meta_getLevel(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkHEqRefl___closed__1;
x_13 = l_Lean_mkConst(x_12, x_11);
x_14 = l_Lean_mkAppB(x_13, x_5, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkHEqRefl___closed__1;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppB(x_20, x_5, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
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
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_1__infer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_whnfD(x_5, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_1);
x_4 = l_Lean_indentExpr(x_3);
x_5 = l_Lean_MessageData_ofList___closed__3;
x_6 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_KernelException_toMessageData___closed__12;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_indentExpr(x_9);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symm");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqSymm___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqSymm___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_mkEqRefl___closed__2;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_eq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_8);
x_20 = l_Lean_Meta_mkEqSymm___closed__5;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_mkEqSymm___closed__2;
x_23 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_6);
x_24 = l_Lean_Expr_appFn_x21(x_8);
x_25 = l_Lean_Expr_appFn_x21(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_28 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_26);
x_29 = l_Lean_Meta_getLevel(x_26, x_2, x_9);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_mkEqSymm___closed__2;
x_35 = l_Lean_mkConst(x_34, x_33);
x_36 = l_Lean_mkApp4(x_35, x_26, x_27, x_28, x_1);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_mkEqSymm___closed__2;
x_42 = l_Lean_mkConst(x_41, x_40);
x_43 = l_Lean_mkApp4(x_42, x_26, x_27, x_28, x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = l_Lean_Expr_eq_x3f___closed__2;
x_52 = lean_unsigned_to_nat(3u);
x_53 = l_Lean_Expr_isAppOfArity___main(x_49, x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
lean_dec(x_2);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_56);
lean_ctor_set(x_59, 3, x_58);
x_60 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_49);
x_61 = l_Lean_Meta_mkEqSymm___closed__5;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Meta_mkEqSymm___closed__2;
x_64 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_50);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = l_Lean_Expr_appFn_x21(x_49);
x_67 = l_Lean_Expr_appFn_x21(x_66);
x_68 = l_Lean_Expr_appArg_x21(x_67);
lean_dec(x_67);
x_69 = l_Lean_Expr_appArg_x21(x_66);
lean_dec(x_66);
x_70 = l_Lean_Expr_appArg_x21(x_49);
lean_dec(x_49);
lean_inc(x_68);
x_71 = l_Lean_Meta_getLevel(x_68, x_2, x_50);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Meta_mkEqSymm___closed__2;
x_78 = l_Lean_mkConst(x_77, x_76);
x_79 = l_Lean_mkApp4(x_78, x_68, x_69, x_70, x_1);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_74;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_1);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
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
lean_dec(x_2);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_1);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
lean_object* _init_l_Lean_Meta_mkEqTrans___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trans");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqTrans___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_mkEqRefl___closed__2;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isAppOf(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_58; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_90 = l_Lean_Expr_eq_x3f___closed__2;
x_91 = lean_unsigned_to_nat(3u);
x_92 = l_Lean_Expr_isAppOfArity___main(x_9, x_90, x_91);
x_93 = l_Lean_Expr_isAppOfArity___main(x_13, x_90, x_91);
if (x_92 == 0)
{
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
x_94 = lean_ctor_get(x_14, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_14, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 0);
lean_inc(x_97);
lean_dec(x_3);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_95);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_98);
x_100 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_9);
x_101 = l_Lean_Meta_mkEqSymm___closed__5;
x_102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Meta_mkEqTrans___closed__2;
x_104 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_14);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = lean_box(0);
x_58 = x_106;
goto block_89;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = l_Lean_Expr_appFn_x21(x_9);
x_108 = l_Lean_Expr_appFn_x21(x_107);
x_109 = l_Lean_Expr_appArg_x21(x_108);
lean_dec(x_108);
x_110 = l_Lean_Expr_appArg_x21(x_107);
lean_dec(x_107);
x_111 = l_Lean_Expr_appArg_x21(x_9);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
if (x_93 == 0)
{
lean_object* x_114; 
lean_dec(x_11);
lean_dec(x_9);
x_114 = lean_box(0);
x_16 = x_114;
x_17 = x_113;
goto block_57;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_113);
x_58 = x_115;
goto block_89;
}
}
block_57:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_13);
x_26 = l_Lean_Meta_mkEqSymm___closed__5;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Meta_mkEqTrans___closed__2;
x_29 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_24);
if (lean_is_scalar(x_15)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_15;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_15);
lean_dec(x_13);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
lean_inc(x_33);
x_37 = l_Lean_Meta_getLevel(x_33, x_3, x_14);
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
x_43 = l_Lean_mkConst(x_42, x_41);
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
x_50 = l_Lean_mkConst(x_49, x_48);
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
block_89:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_59 = lean_ctor_get(x_14, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec(x_3);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_64, 2, x_61);
lean_ctor_set(x_64, 3, x_63);
x_65 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_9);
x_66 = l_Lean_Meta_mkEqSymm___closed__5;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_mkEqTrans___closed__2;
x_69 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_64);
if (lean_is_scalar(x_11)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_11;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_14);
return x_70;
}
else
{
uint8_t x_71; 
lean_dec(x_11);
lean_dec(x_9);
x_71 = !lean_is_exclusive(x_58);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_58, 0);
x_73 = l_Lean_Expr_appFn_x21(x_13);
x_74 = l_Lean_Expr_appFn_x21(x_73);
x_75 = l_Lean_Expr_appArg_x21(x_74);
lean_dec(x_74);
x_76 = l_Lean_Expr_appArg_x21(x_73);
lean_dec(x_73);
x_77 = l_Lean_Expr_appArg_x21(x_13);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_58, 0, x_79);
x_16 = x_58;
x_17 = x_72;
goto block_57;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_58, 0);
lean_inc(x_80);
lean_dec(x_58);
x_81 = l_Lean_Expr_appFn_x21(x_13);
x_82 = l_Lean_Expr_appFn_x21(x_81);
x_83 = l_Lean_Expr_appArg_x21(x_82);
lean_dec(x_82);
x_84 = l_Lean_Expr_appArg_x21(x_81);
lean_dec(x_81);
x_85 = l_Lean_Expr_appArg_x21(x_13);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_83);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_16 = x_88;
x_17 = x_80;
goto block_57;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_12);
if (x_116 == 0)
{
return x_12;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_12, 0);
x_118 = lean_ctor_get(x_12, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_8);
if (x_120 == 0)
{
return x_8;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_8, 0);
x_122 = lean_ctor_get(x_8, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_8);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_4);
return x_124;
}
}
else
{
lean_object* x_125; 
lean_dec(x_3);
lean_dec(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_125, 1, x_4);
return x_125;
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality proof expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHEqSymm___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkHEqSymm___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkHEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_mkHEqRefl___closed__1;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_heq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_8);
x_20 = l_Lean_Meta_mkHEqSymm___closed__4;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_mkHEqSymm___closed__1;
x_23 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_6);
x_24 = l_Lean_Expr_appFn_x21(x_8);
x_25 = l_Lean_Expr_appFn_x21(x_24);
x_26 = l_Lean_Expr_appFn_x21(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_29 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_30 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_27);
x_31 = l_Lean_Meta_getLevel(x_27, x_2, x_9);
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
x_36 = l_Lean_Meta_mkHEqSymm___closed__1;
x_37 = l_Lean_mkConst(x_36, x_35);
x_38 = l_Lean_mkApp5(x_37, x_27, x_29, x_28, x_30, x_1);
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
x_43 = l_Lean_Meta_mkHEqSymm___closed__1;
x_44 = l_Lean_mkConst(x_43, x_42);
x_45 = l_Lean_mkApp5(x_44, x_27, x_29, x_28, x_30, x_1);
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
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = l_Lean_Expr_heq_x3f___closed__2;
x_54 = lean_unsigned_to_nat(4u);
x_55 = l_Lean_Expr_isAppOfArity___main(x_51, x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
x_62 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_51);
x_63 = l_Lean_Meta_mkHEqSymm___closed__4;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Lean_Meta_mkHEqSymm___closed__1;
x_66 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_61);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_52);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = l_Lean_Expr_appFn_x21(x_51);
x_69 = l_Lean_Expr_appFn_x21(x_68);
x_70 = l_Lean_Expr_appFn_x21(x_69);
x_71 = l_Lean_Expr_appArg_x21(x_70);
lean_dec(x_70);
x_72 = l_Lean_Expr_appArg_x21(x_69);
lean_dec(x_69);
x_73 = l_Lean_Expr_appArg_x21(x_68);
lean_dec(x_68);
x_74 = l_Lean_Expr_appArg_x21(x_51);
lean_dec(x_51);
lean_inc(x_71);
x_75 = l_Lean_Meta_getLevel(x_71, x_2, x_52);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_mkHEqSymm___closed__1;
x_82 = l_Lean_mkConst(x_81, x_80);
x_83 = l_Lean_mkApp5(x_82, x_71, x_73, x_72, x_74, x_1);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_78;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_1);
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_75, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_87 = x_75;
} else {
 lean_dec_ref(x_75);
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
}
else
{
uint8_t x_89; 
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
return x_6;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_6, 0);
x_91 = lean_ctor_get(x_6, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_6);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_3);
return x_93;
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqTrans___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkHEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_mkHEqRefl___closed__1;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isAppOf(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_62; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_100 = l_Lean_Expr_heq_x3f___closed__2;
x_101 = lean_unsigned_to_nat(4u);
x_102 = l_Lean_Expr_isAppOfArity___main(x_9, x_100, x_101);
x_103 = l_Lean_Expr_isAppOfArity___main(x_13, x_100, x_101);
if (x_102 == 0)
{
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
x_104 = lean_ctor_get(x_14, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_14, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 0);
lean_inc(x_107);
lean_dec(x_3);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_108);
x_110 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_9);
x_111 = l_Lean_Meta_mkHEqSymm___closed__4;
x_112 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = l_Lean_Meta_mkHEqTrans___closed__1;
x_114 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_109);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_14);
return x_115;
}
else
{
lean_object* x_116; 
x_116 = lean_box(0);
x_62 = x_116;
goto block_99;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = l_Lean_Expr_appFn_x21(x_9);
x_118 = l_Lean_Expr_appFn_x21(x_117);
x_119 = l_Lean_Expr_appFn_x21(x_118);
x_120 = l_Lean_Expr_appArg_x21(x_119);
lean_dec(x_119);
x_121 = l_Lean_Expr_appArg_x21(x_118);
lean_dec(x_118);
x_122 = l_Lean_Expr_appArg_x21(x_117);
lean_dec(x_117);
x_123 = l_Lean_Expr_appArg_x21(x_9);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_120);
lean_ctor_set(x_126, 1, x_125);
if (x_103 == 0)
{
lean_object* x_127; 
lean_dec(x_11);
lean_dec(x_9);
x_127 = lean_box(0);
x_16 = x_127;
x_17 = x_126;
goto block_61;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_126);
x_62 = x_128;
goto block_99;
}
}
block_61:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_1);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_13);
x_27 = l_Lean_Meta_mkHEqSymm___closed__4;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_mkHEqTrans___closed__1;
x_30 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_25);
if (lean_is_scalar(x_15)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_15;
 lean_ctor_set_tag(x_31, 1);
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_14);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_15);
lean_dec(x_13);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_ctor_get(x_34, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
lean_inc(x_35);
x_41 = l_Lean_Meta_getLevel(x_35, x_3, x_14);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_mkHEqTrans___closed__1;
x_47 = l_Lean_mkConst(x_46, x_45);
x_48 = l_Lean_mkApp8(x_47, x_35, x_37, x_39, x_36, x_38, x_40, x_1, x_2);
lean_ctor_set(x_41, 0, x_48);
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_mkHEqTrans___closed__1;
x_54 = l_Lean_mkConst(x_53, x_52);
x_55 = l_Lean_mkApp8(x_54, x_35, x_37, x_39, x_36, x_38, x_40, x_1, x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_41, 0);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_41);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
block_99:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_67);
x_69 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_9);
x_70 = l_Lean_Meta_mkHEqSymm___closed__4;
x_71 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_Lean_Meta_mkHEqTrans___closed__1;
x_73 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
lean_ctor_set(x_73, 2, x_68);
if (lean_is_scalar(x_11)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_11;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_14);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_11);
lean_dec(x_9);
x_75 = !lean_is_exclusive(x_62);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = l_Lean_Expr_appFn_x21(x_13);
x_78 = l_Lean_Expr_appFn_x21(x_77);
x_79 = l_Lean_Expr_appFn_x21(x_78);
x_80 = l_Lean_Expr_appArg_x21(x_79);
lean_dec(x_79);
x_81 = l_Lean_Expr_appArg_x21(x_78);
lean_dec(x_78);
x_82 = l_Lean_Expr_appArg_x21(x_77);
lean_dec(x_77);
x_83 = l_Lean_Expr_appArg_x21(x_13);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_62, 0, x_86);
x_16 = x_62;
x_17 = x_76;
goto block_61;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = lean_ctor_get(x_62, 0);
lean_inc(x_87);
lean_dec(x_62);
x_88 = l_Lean_Expr_appFn_x21(x_13);
x_89 = l_Lean_Expr_appFn_x21(x_88);
x_90 = l_Lean_Expr_appFn_x21(x_89);
x_91 = l_Lean_Expr_appArg_x21(x_90);
lean_dec(x_90);
x_92 = l_Lean_Expr_appArg_x21(x_89);
lean_dec(x_89);
x_93 = l_Lean_Expr_appArg_x21(x_88);
lean_dec(x_88);
x_94 = l_Lean_Expr_appArg_x21(x_13);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_91);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_16 = x_98;
x_17 = x_87;
goto block_61;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_12);
if (x_129 == 0)
{
return x_12;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_12, 0);
x_131 = lean_ctor_get(x_12, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_12);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_8);
if (x_133 == 0)
{
return x_8;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; 
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_1);
lean_ctor_set(x_137, 1, x_4);
return x_137;
}
}
else
{
lean_object* x_138; 
lean_dec(x_3);
lean_dec(x_1);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_4);
return x_138;
}
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("eqOfHEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkEqOfHEq___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality types are not definitionally equal");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("is not definitionally equal to");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqOfHEq___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_Expr_heq_x3f___closed__2;
x_9 = lean_unsigned_to_nat(4u);
x_10 = l_Lean_Expr_isAppOfArity___main(x_6, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_indentExpr(x_17);
x_19 = l_Lean_Meta_mkHEqSymm___closed__4;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_mkHEqTrans___closed__1;
x_22 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_16);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_4);
x_23 = l_Lean_Expr_appFn_x21(x_6);
x_24 = l_Lean_Expr_appFn_x21(x_23);
x_25 = l_Lean_Expr_appFn_x21(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_28 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_29 = l_Lean_Expr_appArg_x21(x_6);
lean_dec(x_6);
lean_inc(x_2);
lean_inc(x_28);
lean_inc(x_26);
x_30 = l_Lean_Meta_isExprDefEq(x_26, x_28, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec(x_2);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_26);
x_43 = l_Lean_indentExpr(x_42);
x_44 = l_Lean_Meta_mkEqOfHEq___closed__5;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_MessageData_ofList___closed__3;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_mkEqOfHEq___closed__8;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_28);
x_51 = l_Lean_indentExpr(x_50);
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_54 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_41);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_54);
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_dec(x_30);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 0);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_26);
x_63 = l_Lean_indentExpr(x_62);
x_64 = l_Lean_Meta_mkEqOfHEq___closed__5;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_MessageData_ofList___closed__3;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_mkEqOfHEq___closed__8;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_28);
x_71 = l_Lean_indentExpr(x_70);
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_74 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_61);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_55);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_28);
x_76 = lean_ctor_get(x_30, 1);
lean_inc(x_76);
lean_dec(x_30);
lean_inc(x_26);
x_77 = l_Lean_Meta_getLevel(x_26, x_2, x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_83 = l_Lean_mkConst(x_82, x_81);
x_84 = l_Lean_mkApp4(x_83, x_26, x_27, x_29, x_1);
lean_ctor_set(x_77, 0, x_84);
return x_77;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_77, 0);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_77);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_90 = l_Lean_mkConst(x_89, x_88);
x_91 = l_Lean_mkApp4(x_90, x_26, x_27, x_29, x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_77);
if (x_93 == 0)
{
return x_77;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_77, 0);
x_95 = lean_ctor_get(x_77, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_77);
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
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_30);
if (x_97 == 0)
{
return x_30;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_30, 0);
x_99 = lean_ctor_get(x_30, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_30);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
x_103 = l_Lean_Expr_heq_x3f___closed__2;
x_104 = lean_unsigned_to_nat(4u);
x_105 = l_Lean_Expr_isAppOfArity___main(x_101, x_103, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_101);
x_106 = lean_ctor_get(x_102, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
lean_dec(x_2);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_107);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_1);
x_113 = l_Lean_indentExpr(x_112);
x_114 = l_Lean_Meta_mkHEqSymm___closed__4;
x_115 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_116 = l_Lean_Meta_mkHEqTrans___closed__1;
x_117 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_102);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_119 = l_Lean_Expr_appFn_x21(x_101);
x_120 = l_Lean_Expr_appFn_x21(x_119);
x_121 = l_Lean_Expr_appFn_x21(x_120);
x_122 = l_Lean_Expr_appArg_x21(x_121);
lean_dec(x_121);
x_123 = l_Lean_Expr_appArg_x21(x_120);
lean_dec(x_120);
x_124 = l_Lean_Expr_appArg_x21(x_119);
lean_dec(x_119);
x_125 = l_Lean_Expr_appArg_x21(x_101);
lean_dec(x_101);
lean_inc(x_2);
lean_inc(x_124);
lean_inc(x_122);
x_126 = l_Lean_Meta_isExprDefEq(x_122, x_124, x_2, x_102);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_1);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_2, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 0);
lean_inc(x_134);
lean_dec(x_2);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_136, 0, x_131);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set(x_136, 2, x_133);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_137, 0, x_122);
x_138 = l_Lean_indentExpr(x_137);
x_139 = l_Lean_Meta_mkEqOfHEq___closed__5;
x_140 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_MessageData_ofList___closed__3;
x_142 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_Meta_mkEqOfHEq___closed__8;
x_144 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_124);
x_146 = l_Lean_indentExpr(x_145);
x_147 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_149 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_149, 2, x_136);
if (lean_is_scalar(x_130)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_130;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_129);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_124);
x_151 = lean_ctor_get(x_126, 1);
lean_inc(x_151);
lean_dec(x_126);
lean_inc(x_122);
x_152 = l_Lean_Meta_getLevel(x_122, x_2, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Meta_mkEqOfHEq___closed__2;
x_159 = l_Lean_mkConst(x_158, x_157);
x_160 = l_Lean_mkApp4(x_159, x_122, x_123, x_125, x_1);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_154);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_1);
x_162 = lean_ctor_get(x_152, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_152, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_164 = x_152;
} else {
 lean_dec_ref(x_152);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_126, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_126, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_168 = x_126;
} else {
 lean_dec_ref(x_126);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_4);
if (x_170 == 0)
{
return x_4;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_4, 0);
x_172 = lean_ctor_get(x_4, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_4);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrArg");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrArg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non-dependent function expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrArg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l___private_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_63; lean_object* x_79; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_111 = l_Lean_Expr_eq_x3f___closed__2;
x_112 = lean_unsigned_to_nat(3u);
x_113 = l_Lean_Expr_isAppOfArity___main(x_6, x_111, x_112);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_ctor_get(x_10, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_10, 2);
lean_inc(x_115);
x_116 = l_Lean_Expr_hasLooseBVars(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (x_113 == 0)
{
x_63 = x_118;
goto block_78;
}
else
{
lean_dec(x_8);
x_79 = x_118;
goto block_110;
}
}
else
{
lean_object* x_119; 
lean_dec(x_115);
lean_dec(x_114);
x_119 = lean_box(0);
if (x_113 == 0)
{
x_63 = x_119;
goto block_78;
}
else
{
lean_dec(x_8);
x_79 = x_119;
goto block_110;
}
}
}
else
{
lean_object* x_120; 
x_120 = lean_box(0);
if (x_113 == 0)
{
x_63 = x_120;
goto block_78;
}
else
{
lean_dec(x_8);
x_79 = x_120;
goto block_110;
}
}
block_62:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_6);
x_22 = l_Lean_Meta_mkEqSymm___closed__5;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_mkCongrArg___closed__2;
x_25 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_12;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_6);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_inc(x_3);
lean_inc(x_29);
x_33 = l_Lean_Meta_getLevel(x_29, x_3, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_30);
x_36 = l_Lean_Meta_getLevel(x_30, x_3, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_mkCongrArg___closed__2;
x_43 = l_Lean_mkConst(x_42, x_41);
x_44 = l_Lean_mkApp6(x_43, x_29, x_30, x_31, x_32, x_1, x_2);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_mkCongrArg___closed__2;
x_51 = l_Lean_mkConst(x_50, x_49);
x_52 = l_Lean_mkApp6(x_51, x_29, x_30, x_31, x_32, x_1, x_2);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
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
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
block_78:
{
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_64 = lean_ctor_get(x_11, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_11, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec(x_3);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_71 = l_Lean_Meta_mkCongrArg___closed__5;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Meta_mkCongrArg___closed__2;
x_74 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_69);
if (lean_is_scalar(x_8)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_8;
 lean_ctor_set_tag(x_75, 1);
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_11);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_10);
lean_dec(x_8);
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
lean_dec(x_63);
x_77 = lean_box(0);
x_13 = x_77;
x_14 = x_76;
goto block_62;
}
}
block_110:
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_2);
x_80 = lean_ctor_get(x_11, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_11, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 2, x_82);
lean_ctor_set(x_85, 3, x_84);
x_86 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_87 = l_Lean_Meta_mkCongrArg___closed__5;
x_88 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Lean_Meta_mkCongrArg___closed__2;
x_90 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_85);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_11);
return x_91;
}
else
{
uint8_t x_92; 
lean_dec(x_10);
x_92 = !lean_is_exclusive(x_79);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_93 = lean_ctor_get(x_79, 0);
x_94 = l_Lean_Expr_appFn_x21(x_6);
x_95 = l_Lean_Expr_appFn_x21(x_94);
x_96 = l_Lean_Expr_appArg_x21(x_95);
lean_dec(x_95);
x_97 = l_Lean_Expr_appArg_x21(x_94);
lean_dec(x_94);
x_98 = l_Lean_Expr_appArg_x21(x_6);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_79, 0, x_100);
x_13 = x_79;
x_14 = x_93;
goto block_62;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_79, 0);
lean_inc(x_101);
lean_dec(x_79);
x_102 = l_Lean_Expr_appFn_x21(x_6);
x_103 = l_Lean_Expr_appFn_x21(x_102);
x_104 = l_Lean_Expr_appArg_x21(x_103);
lean_dec(x_103);
x_105 = l_Lean_Expr_appArg_x21(x_102);
lean_dec(x_102);
x_106 = l_Lean_Expr_appArg_x21(x_6);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_13 = x_109;
x_14 = x_101;
goto block_62;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_9);
if (x_121 == 0)
{
return x_9;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_9, 0);
x_123 = lean_ctor_get(x_9, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_9);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_5);
if (x_125 == 0)
{
return x_5;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_5, 0);
x_127 = lean_ctor_get(x_5, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_5);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrFun");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof between functions expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrFun___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkCongrFun___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_eq_x3f___closed__2;
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity___main(x_7, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_16);
x_18 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_7);
x_19 = l_Lean_Meta_mkEqSymm___closed__5;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_mkCongrFun___closed__2;
x_22 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_22);
return x_5;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_5);
x_23 = l_Lean_Expr_appFn_x21(x_7);
x_24 = l_Lean_Expr_appFn_x21(x_23);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_27 = l_Lean_Expr_appArg_x21(x_7);
lean_inc(x_3);
x_28 = l_Lean_Meta_whnfD(x_25, x_3, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_obj_tag(x_29) == 7)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_31);
lean_dec(x_7);
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_29, 2);
lean_inc(x_48);
lean_dec(x_29);
x_49 = 0;
lean_inc(x_47);
x_50 = l_Lean_mkLambda(x_46, x_49, x_47, x_48);
lean_dec(x_46);
lean_inc(x_3);
lean_inc(x_47);
x_51 = l_Lean_Meta_getLevel(x_47, x_3, x_30);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_2);
lean_inc(x_50);
x_54 = l_Lean_mkApp(x_50, x_2);
x_55 = l_Lean_Meta_getLevel(x_54, x_3, x_53);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_mkCongrFun___closed__2;
x_62 = l_Lean_mkConst(x_61, x_60);
x_63 = l_Lean_mkApp6(x_62, x_47, x_50, x_26, x_27, x_1, x_2);
lean_ctor_set(x_55, 0, x_63);
return x_55;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_55);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_mkCongrFun___closed__2;
x_70 = l_Lean_mkConst(x_69, x_68);
x_71 = l_Lean_mkApp6(x_70, x_47, x_50, x_26, x_27, x_1, x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_51);
if (x_77 == 0)
{
return x_51;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_51, 0);
x_79 = lean_ctor_get(x_51, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_51);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_81 = lean_box(0);
x_32 = x_81;
goto block_45;
}
block_45:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_7);
x_40 = l_Lean_Meta_mkCongrFun___closed__5;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Meta_mkCongrFun___closed__2;
x_43 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_38);
if (lean_is_scalar(x_31)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_31;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_30);
return x_44;
}
}
else
{
uint8_t x_82; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_28);
if (x_82 == 0)
{
return x_28;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_28, 0);
x_84 = lean_ctor_get(x_28, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_28);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_5);
x_88 = l_Lean_Expr_eq_x3f___closed__2;
x_89 = lean_unsigned_to_nat(3u);
x_90 = l_Lean_Expr_isAppOfArity___main(x_86, x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_3, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_3, 0);
lean_inc(x_94);
lean_dec(x_3);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_91);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_95);
x_97 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_86);
x_98 = l_Lean_Meta_mkEqSymm___closed__5;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Meta_mkCongrFun___closed__2;
x_101 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_96);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_87);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = l_Lean_Expr_appFn_x21(x_86);
x_104 = l_Lean_Expr_appFn_x21(x_103);
x_105 = l_Lean_Expr_appArg_x21(x_104);
lean_dec(x_104);
x_106 = l_Lean_Expr_appArg_x21(x_103);
lean_dec(x_103);
x_107 = l_Lean_Expr_appArg_x21(x_86);
lean_inc(x_3);
x_108 = l_Lean_Meta_whnfD(x_105, x_3, x_87);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_obj_tag(x_109) == 7)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_111);
lean_dec(x_86);
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_109, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_109, 2);
lean_inc(x_128);
lean_dec(x_109);
x_129 = 0;
lean_inc(x_127);
x_130 = l_Lean_mkLambda(x_126, x_129, x_127, x_128);
lean_dec(x_126);
lean_inc(x_3);
lean_inc(x_127);
x_131 = l_Lean_Meta_getLevel(x_127, x_3, x_110);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_2);
lean_inc(x_130);
x_134 = l_Lean_mkApp(x_130, x_2);
x_135 = l_Lean_Meta_getLevel(x_134, x_3, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_box(0);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Meta_mkCongrFun___closed__2;
x_143 = l_Lean_mkConst(x_142, x_141);
x_144 = l_Lean_mkApp6(x_143, x_127, x_130, x_106, x_107, x_1, x_2);
if (lean_is_scalar(x_138)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_138;
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_137);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_130);
lean_dec(x_127);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = lean_ctor_get(x_131, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_131, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_152 = x_131;
} else {
 lean_dec_ref(x_131);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_2);
x_154 = lean_box(0);
x_112 = x_154;
goto block_125;
}
block_125:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_112);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_3, 0);
lean_inc(x_116);
lean_dec(x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_114);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_117);
x_119 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_86);
x_120 = l_Lean_Meta_mkCongrFun___closed__5;
x_121 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
x_122 = l_Lean_Meta_mkCongrFun___closed__2;
x_123 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_118);
if (lean_is_scalar(x_111)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_111;
 lean_ctor_set_tag(x_124, 1);
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_110);
return x_124;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_86);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_108, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_108, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_157 = x_108;
} else {
 lean_dec_ref(x_108);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_5);
if (x_159 == 0)
{
return x_5;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_5, 0);
x_161 = lean_ctor_get(x_5, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_5);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congr");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_92; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_124 = l_Lean_Expr_eq_x3f___closed__2;
x_125 = lean_unsigned_to_nat(3u);
x_126 = l_Lean_Expr_isAppOfArity___main(x_6, x_124, x_125);
x_127 = l_Lean_Expr_isAppOfArity___main(x_10, x_124, x_125);
if (x_126 == 0)
{
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
x_128 = lean_ctor_get(x_11, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_11, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_3, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_3, 0);
lean_inc(x_131);
lean_dec(x_3);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_129);
lean_ctor_set(x_133, 2, x_130);
lean_ctor_set(x_133, 3, x_132);
x_134 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_6);
x_135 = l_Lean_Meta_mkEqSymm___closed__5;
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_Meta_mkCongr___closed__2;
x_138 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_133);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_11);
return x_139;
}
else
{
lean_object* x_140; 
x_140 = lean_box(0);
x_92 = x_140;
goto block_123;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = l_Lean_Expr_appFn_x21(x_6);
x_142 = l_Lean_Expr_appFn_x21(x_141);
x_143 = l_Lean_Expr_appArg_x21(x_142);
lean_dec(x_142);
x_144 = l_Lean_Expr_appArg_x21(x_141);
lean_dec(x_141);
x_145 = l_Lean_Expr_appArg_x21(x_6);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
if (x_127 == 0)
{
lean_object* x_148; 
lean_dec(x_8);
x_148 = lean_box(0);
x_13 = x_148;
x_14 = x_147;
goto block_91;
}
else
{
lean_object* x_149; 
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_147);
x_92 = x_149;
goto block_123;
}
}
block_91:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_10);
x_23 = l_Lean_Meta_mkEqSymm___closed__5;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_mkCongr___closed__2;
x_26 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_21);
if (lean_is_scalar(x_12)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_12;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_10);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
lean_inc(x_3);
x_36 = l_Lean_Meta_whnfD(x_30, x_3, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
if (lean_obj_tag(x_37) == 7)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_37, 2);
lean_inc(x_54);
lean_dec(x_37);
x_55 = l_Lean_Expr_hasLooseBVars(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_6);
lean_inc(x_3);
lean_inc(x_33);
x_56 = l_Lean_Meta_getLevel(x_33, x_3, x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_54);
x_59 = l_Lean_Meta_getLevel(x_54, x_3, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_mkCongr___closed__2;
x_66 = l_Lean_mkConst(x_65, x_64);
x_67 = l_Lean_mkApp8(x_66, x_33, x_54, x_31, x_32, x_34, x_35, x_1, x_2);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_mkCongr___closed__2;
x_74 = l_Lean_mkConst(x_73, x_72);
x_75 = l_Lean_mkApp8(x_74, x_33, x_54, x_31, x_32, x_34, x_35, x_1, x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_59);
if (x_77 == 0)
{
return x_59;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_59, 0);
x_79 = lean_ctor_get(x_59, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_59);
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
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
return x_56;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_56, 0);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_56);
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
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_85 = lean_box(0);
x_40 = x_85;
goto block_53;
}
}
else
{
lean_object* x_86; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_2);
x_86 = lean_box(0);
x_40 = x_86;
goto block_53;
}
block_53:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 0);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_6);
x_48 = l_Lean_Meta_mkCongrArg___closed__5;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_mkCongr___closed__2;
x_51 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_39;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
}
else
{
uint8_t x_87; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_36);
if (x_87 == 0)
{
return x_36;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_36, 0);
x_89 = lean_ctor_get(x_36, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_36);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
block_123:
{
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_2);
x_93 = lean_ctor_get(x_11, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_3, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_3, 0);
lean_inc(x_96);
lean_dec(x_3);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_94);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_97);
x_99 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_6);
x_100 = l_Lean_Meta_mkEqSymm___closed__5;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Meta_mkCongr___closed__2;
x_103 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_98);
if (lean_is_scalar(x_8)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_8;
 lean_ctor_set_tag(x_104, 1);
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_11);
return x_104;
}
else
{
uint8_t x_105; 
lean_dec(x_8);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_106 = lean_ctor_get(x_92, 0);
x_107 = l_Lean_Expr_appFn_x21(x_10);
x_108 = l_Lean_Expr_appFn_x21(x_107);
x_109 = l_Lean_Expr_appArg_x21(x_108);
lean_dec(x_108);
x_110 = l_Lean_Expr_appArg_x21(x_107);
lean_dec(x_107);
x_111 = l_Lean_Expr_appArg_x21(x_10);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_92, 0, x_113);
x_13 = x_92;
x_14 = x_106;
goto block_91;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_92, 0);
lean_inc(x_114);
lean_dec(x_92);
x_115 = l_Lean_Expr_appFn_x21(x_10);
x_116 = l_Lean_Expr_appFn_x21(x_115);
x_117 = l_Lean_Expr_appArg_x21(x_116);
lean_dec(x_116);
x_118 = l_Lean_Expr_appArg_x21(x_115);
lean_dec(x_115);
x_119 = l_Lean_Expr_appArg_x21(x_10);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_13 = x_122;
x_14 = x_114;
goto block_91;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_9);
if (x_150 == 0)
{
return x_9;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_9, 0);
x_152 = lean_ctor_get(x_9, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_9);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_5);
if (x_154 == 0)
{
return x_5;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_5, 0);
x_156 = lean_ctor_get(x_5, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_5);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_9);
x_10 = l_Lean_Meta_getMVarDecl(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l_Lean_Meta_synthInstance(x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_assignExprMVar(x_9, x_15, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
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
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result contains metavariables");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1(x_4, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_7, x_2);
x_11 = l_Lean_Meta_instantiateMVars(x_10, x_5, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_hasAssignableMVar(x_12, x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_12);
x_31 = l_Lean_indentExpr(x_30);
x_32 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_5, 0);
lean_inc(x_39);
lean_dec(x_5);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_12);
x_43 = l_Lean_indentExpr(x_42);
x_44 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_41);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Lean_Meta_AppBuilder_3__mkAppMFinal___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppM");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit arguments provided to");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_132; lean_object* x_133; 
x_77 = lean_ctor_get(x_7, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_7, 2);
lean_inc(x_79);
x_80 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_81 = lean_array_get_size(x_4);
x_82 = lean_expr_instantiate_rev_range(x_78, x_5, x_81, x_4);
lean_dec(x_81);
lean_dec(x_78);
x_132 = (uint8_t)((x_80 << 24) >> 61);
x_133 = lean_box(x_132);
switch (lean_obj_tag(x_133)) {
case 1:
{
uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = 0;
lean_inc(x_8);
x_135 = l_Lean_Meta_mkFreshExprMVar(x_82, x_77, x_134, x_8, x_9);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_array_push(x_4, x_136);
x_4 = x_138;
x_7 = x_79;
x_9 = x_137;
goto _start;
}
case 3:
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_140 = 1;
lean_inc(x_8);
x_141 = l_Lean_Meta_mkFreshExprMVar(x_82, x_77, x_140, x_8, x_9);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
lean_inc(x_142);
x_144 = lean_array_push(x_4, x_142);
x_145 = l_Lean_Expr_mvarId_x21(x_142);
lean_dec(x_142);
x_146 = lean_array_push(x_6, x_145);
x_4 = x_144;
x_6 = x_146;
x_7 = x_79;
x_9 = x_143;
goto _start;
}
default: 
{
lean_object* x_148; 
lean_dec(x_133);
lean_dec(x_77);
x_148 = lean_box(0);
x_83 = x_148;
goto block_131;
}
}
block_131:
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_83);
x_84 = lean_array_get_size(x_2);
x_85 = lean_nat_dec_lt(x_3, x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_5);
lean_dec(x_3);
x_86 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
x_87 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_86, x_1, x_4, x_6, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_array_fget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_88);
x_89 = l_Lean_Meta_inferType(x_88, x_8, x_9);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_8);
x_92 = l_Lean_Meta_isExprDefEq(x_82, x_90, x_8, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
uint8_t x_95; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_96 = lean_ctor_get(x_92, 1);
x_97 = lean_ctor_get(x_92, 0);
lean_dec(x_97);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_8, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_8, 0);
lean_inc(x_101);
lean_dec(x_8);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_104, x_1);
lean_dec(x_4);
x_106 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_88);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set_tag(x_92, 1);
lean_ctor_set(x_92, 0, x_106);
return x_92;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_92, 1);
lean_inc(x_107);
lean_dec(x_92);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_8, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
lean_dec(x_8);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_109);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_114, x_1);
lean_dec(x_4);
x_116 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_88);
lean_ctor_set(x_116, 2, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_107);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_92, 1);
lean_inc(x_118);
lean_dec(x_92);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_add(x_3, x_119);
lean_dec(x_3);
x_121 = lean_array_push(x_4, x_88);
x_3 = x_120;
x_4 = x_121;
x_7 = x_79;
x_9 = x_118;
goto _start;
}
}
else
{
uint8_t x_123; 
lean_dec(x_88);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_92);
if (x_123 == 0)
{
return x_92;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_92, 0);
x_125 = lean_ctor_get(x_92, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_92);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_88);
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_89);
if (x_127 == 0)
{
return x_89;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_89, 0);
x_129 = lean_ctor_get(x_89, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_89);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
}
else
{
lean_object* x_149; 
x_149 = lean_box(0);
x_10 = x_149;
goto block_76;
}
block_76:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_4);
x_12 = lean_expr_instantiate_rev_range(x_7, x_5, x_11, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_8);
x_13 = l_Lean_Meta_whnfD(x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_isForall(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_11);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_eq(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_indentExpr(x_26);
x_28 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_MessageData_ofList___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_36 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_34, x_35);
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
x_39 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_25);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_free_object(x_13);
x_40 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
x_41 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_40, x_1, x_4, x_6, x_8, x_16);
lean_dec(x_6);
lean_dec(x_4);
return x_41;
}
}
else
{
lean_free_object(x_13);
x_5 = x_11;
x_7 = x_15;
x_9 = x_16;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_13, 0);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_13);
x_45 = l_Lean_Expr_isForall(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_43);
lean_dec(x_11);
x_46 = lean_array_get_size(x_2);
x_47 = lean_nat_dec_eq(x_3, x_46);
lean_dec(x_46);
lean_dec(x_3);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_6);
lean_dec(x_4);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
lean_dec(x_8);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_1);
x_55 = l_Lean_indentExpr(x_54);
x_56 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_MessageData_ofList___closed__3;
x_59 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_64 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_2, x_62, x_63);
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_61);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
x_67 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_53);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_44);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2;
x_70 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_69, x_1, x_4, x_6, x_8, x_44);
lean_dec(x_6);
lean_dec(x_4);
return x_70;
}
}
else
{
x_5 = x_11;
x_7 = x_43;
x_9 = x_44;
goto _start;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_13);
if (x_72 == 0)
{
return x_13;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_13, 0);
x_74 = lean_ctor_get(x_13, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_13);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_4__mkAppMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(x_7, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(x_18, x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_5__mkFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_Meta_getConstInfo(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_ConstantInfo_lparams(x_5);
x_8 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(x_7, x_2, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Lean_mkConst(x_1, x_10);
x_12 = lean_instantiate_type_lparams(x_5, x_10);
lean_dec(x_10);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_14);
x_16 = l_Lean_mkConst(x_1, x_14);
x_17 = lean_instantiate_type_lparams(x_5, x_14);
lean_dec(x_14);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at___private_Lean_Meta_AppBuilder_5__mkFun___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_5__mkFun___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Meta_mkAppM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_12__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_4, 4);
lean_inc(x_364);
x_365 = lean_ctor_get_uint8(x_364, sizeof(void*)*1);
lean_dec(x_364);
if (x_365 == 0)
{
uint8_t x_366; 
x_366 = 0;
x_5 = x_366;
x_6 = x_4;
goto block_363;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_367 = l_Lean_Meta_mkAppM___closed__1;
x_368 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_367, x_3, x_4);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = lean_unbox(x_369);
lean_dec(x_369);
x_5 = x_371;
x_6 = x_370;
goto block_363;
}
block_363:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_12 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_12);
lean_inc(x_10);
x_13 = l_Lean_MetavarContext_incDepth(x_10);
lean_ctor_set(x_6, 1, x_13);
x_14 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_empty___closed__1;
x_21 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_17, x_2, x_19, x_20, x_19, x_20, x_18, x_3, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_11);
lean_ctor_set(x_22, 1, x_10);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_11);
lean_ctor_set(x_22, 4, x_31);
lean_ctor_set(x_22, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 2);
x_34 = lean_ctor_get(x_22, 3);
x_35 = lean_ctor_get(x_22, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_37 = x_23;
} else {
 lean_dec_ref(x_23);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_11);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_21, 1, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_22, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_22, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 5);
lean_inc(x_44);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_45 = x_22;
} else {
 lean_dec_ref(x_22);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_23, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_47 = x_23;
} else {
 lean_dec_ref(x_23);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_10);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 4);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_21, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_51, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_11);
lean_ctor_set(x_51, 1, x_10);
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_11);
lean_ctor_set(x_51, 4, x_60);
lean_ctor_set(x_51, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 2);
x_63 = lean_ctor_get(x_51, 3);
x_64 = lean_ctor_get(x_51, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_11);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_10);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_21, 1, x_68);
return x_21;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_21, 0);
lean_inc(x_69);
lean_dec(x_21);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_51, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_51, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_51, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 x_74 = x_51;
} else {
 lean_dec_ref(x_51);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_76 = x_52;
} else {
 lean_dec_ref(x_52);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 6, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_10);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_3);
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 4);
lean_inc(x_81);
x_82 = !lean_is_exclusive(x_14);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_14, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_80, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_11);
lean_ctor_set(x_80, 1, x_10);
return x_14;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_11);
lean_ctor_set(x_80, 4, x_89);
lean_ctor_set(x_80, 1, x_10);
return x_14;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 2);
x_92 = lean_ctor_get(x_80, 3);
x_93 = lean_ctor_get(x_80, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_95 = x_81;
} else {
 lean_dec_ref(x_81);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_11);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_10);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_96);
lean_ctor_set(x_97, 5, x_93);
lean_ctor_set(x_14, 1, x_97);
return x_14;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_14, 0);
lean_inc(x_98);
lean_dec(x_14);
x_99 = lean_ctor_get(x_80, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_80, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 5);
lean_inc(x_102);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_81, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 1, 1);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_10);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_106);
lean_ctor_set(x_107, 5, x_102);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_6, 1);
x_110 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
lean_dec(x_8);
x_112 = 0;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_inc(x_109);
x_114 = l_Lean_MetavarContext_incDepth(x_109);
lean_ctor_set(x_6, 4, x_113);
lean_ctor_set(x_6, 1, x_114);
x_115 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_6);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Array_empty___closed__1;
x_122 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_118, x_2, x_120, x_121, x_120, x_121, x_119, x_3, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_109);
lean_ctor_set(x_135, 2, x_128);
lean_ctor_set(x_135, 3, x_129);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_130);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_140 = x_122;
} else {
 lean_dec_ref(x_122);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 x_145 = x_137;
} else {
 lean_dec_ref(x_137);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_147 = x_138;
} else {
 lean_dec_ref(x_138);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 1, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_145)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_145;
}
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_109);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_143);
lean_ctor_set(x_149, 4, x_148);
lean_ctor_set(x_149, 5, x_144);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_3);
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_115, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_154 = x_115;
} else {
 lean_dec_ref(x_115);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 5);
lean_inc(x_158);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_159 = x_151;
} else {
 lean_dec_ref(x_151);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_161 = x_152;
} else {
 lean_dec_ref(x_152);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 1, 1);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_159)) {
 x_163 = lean_alloc_ctor(0, 6, 0);
} else {
 x_163 = x_159;
}
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_109);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
lean_ctor_set(x_163, 4, x_162);
lean_ctor_set(x_163, 5, x_158);
if (lean_is_scalar(x_154)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_154;
}
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_6, 4);
x_166 = lean_ctor_get(x_6, 0);
x_167 = lean_ctor_get(x_6, 1);
x_168 = lean_ctor_get(x_6, 2);
x_169 = lean_ctor_get(x_6, 3);
x_170 = lean_ctor_get(x_6, 5);
lean_inc(x_170);
lean_inc(x_165);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_6);
x_171 = lean_ctor_get_uint8(x_165, sizeof(void*)*1);
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
x_174 = 0;
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 1, 1);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
lean_inc(x_167);
x_176 = l_Lean_MetavarContext_incDepth(x_167);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_168);
lean_ctor_set(x_177, 3, x_169);
lean_ctor_set(x_177, 4, x_175);
lean_ctor_set(x_177, 5, x_170);
x_178 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_empty___closed__1;
x_185 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_181, x_2, x_183, x_184, x_183, x_184, x_182, x_3, x_180);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 1, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_167);
lean_ctor_set(x_198, 2, x_191);
lean_ctor_set(x_198, 3, x_192);
lean_ctor_set(x_198, 4, x_197);
lean_ctor_set(x_198, 5, x_193);
if (lean_is_scalar(x_189)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_189;
}
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_185, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_203 = x_185;
} else {
 lean_dec_ref(x_185);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 1);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 6, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_204);
lean_ctor_set(x_212, 1, x_167);
lean_ctor_set(x_212, 2, x_205);
lean_ctor_set(x_212, 3, x_206);
lean_ctor_set(x_212, 4, x_211);
lean_ctor_set(x_212, 5, x_207);
if (lean_is_scalar(x_203)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_203;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_3);
x_214 = lean_ctor_get(x_178, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_178, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_217 = x_178;
} else {
 lean_dec_ref(x_178);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 5);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 lean_ctor_release(x_214, 5);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_215, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_224 = x_215;
} else {
 lean_dec_ref(x_215);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 1, 1);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_222)) {
 x_226 = lean_alloc_ctor(0, 6, 0);
} else {
 x_226 = x_222;
}
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_167);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set(x_226, 4, x_225);
lean_ctor_set(x_226, 5, x_221);
if (lean_is_scalar(x_217)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_217;
}
lean_ctor_set(x_227, 0, x_216);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(x_6);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
x_233 = l_Lean_MetavarContext_incDepth(x_232);
lean_ctor_set(x_229, 1, x_233);
x_234 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_229);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Array_empty___closed__1;
lean_inc(x_3);
x_241 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_237, x_2, x_239, x_240, x_239, x_240, x_238, x_3, x_236);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = !lean_is_exclusive(x_242);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = lean_ctor_get(x_242, 1);
lean_dec(x_245);
lean_ctor_set(x_242, 1, x_232);
x_246 = l_Lean_Meta_mkAppM___closed__1;
x_247 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_246, x_3, x_242);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_247, 0);
lean_dec(x_249);
lean_ctor_set(x_247, 0, x_243);
return x_247;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_242, 0);
x_253 = lean_ctor_get(x_242, 2);
x_254 = lean_ctor_get(x_242, 3);
x_255 = lean_ctor_get(x_242, 4);
x_256 = lean_ctor_get(x_242, 5);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_242);
x_257 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_232);
lean_ctor_set(x_257, 2, x_253);
lean_ctor_set(x_257, 3, x_254);
lean_ctor_set(x_257, 4, x_255);
lean_ctor_set(x_257, 5, x_256);
x_258 = l_Lean_Meta_mkAppM___closed__1;
x_259 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_258, x_3, x_257);
lean_dec(x_3);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_243);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_241, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_241, 0);
lean_inc(x_264);
lean_dec(x_241);
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_263, 1);
lean_dec(x_266);
lean_ctor_set(x_263, 1, x_232);
x_267 = l_Lean_Meta_mkAppM___closed__1;
x_268 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_267, x_3, x_263);
lean_dec(x_3);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set_tag(x_268, 1);
lean_ctor_set(x_268, 0, x_264);
return x_268;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_273 = lean_ctor_get(x_263, 0);
x_274 = lean_ctor_get(x_263, 2);
x_275 = lean_ctor_get(x_263, 3);
x_276 = lean_ctor_get(x_263, 4);
x_277 = lean_ctor_get(x_263, 5);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_263);
x_278 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set(x_278, 1, x_232);
lean_ctor_set(x_278, 2, x_274);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set(x_278, 5, x_277);
x_279 = l_Lean_Meta_mkAppM___closed__1;
x_280 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_279, x_3, x_278);
lean_dec(x_3);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
 lean_ctor_set_tag(x_283, 1);
}
lean_ctor_set(x_283, 0, x_264);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_234, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_234, 0);
lean_inc(x_285);
lean_dec(x_234);
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_287 = lean_ctor_get(x_284, 1);
lean_dec(x_287);
lean_ctor_set(x_284, 1, x_232);
x_288 = l_Lean_Meta_mkAppM___closed__1;
x_289 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_288, x_3, x_284);
lean_dec(x_3);
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_289, 0);
lean_dec(x_291);
lean_ctor_set_tag(x_289, 1);
lean_ctor_set(x_289, 0, x_285);
return x_289;
}
else
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec(x_289);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_285);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_284, 0);
x_295 = lean_ctor_get(x_284, 2);
x_296 = lean_ctor_get(x_284, 3);
x_297 = lean_ctor_get(x_284, 4);
x_298 = lean_ctor_get(x_284, 5);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_284);
x_299 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_232);
lean_ctor_set(x_299, 2, x_295);
lean_ctor_set(x_299, 3, x_296);
lean_ctor_set(x_299, 4, x_297);
lean_ctor_set(x_299, 5, x_298);
x_300 = l_Lean_Meta_mkAppM___closed__1;
x_301 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_300, x_3, x_299);
lean_dec(x_3);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
 lean_ctor_set_tag(x_304, 1);
}
lean_ctor_set(x_304, 0, x_285);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_229, 0);
x_306 = lean_ctor_get(x_229, 1);
x_307 = lean_ctor_get(x_229, 2);
x_308 = lean_ctor_get(x_229, 3);
x_309 = lean_ctor_get(x_229, 4);
x_310 = lean_ctor_get(x_229, 5);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_229);
lean_inc(x_306);
x_311 = l_Lean_MetavarContext_incDepth(x_306);
x_312 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_312, 0, x_305);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_312, 2, x_307);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set(x_312, 4, x_309);
lean_ctor_set(x_312, 5, x_310);
x_313 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_unsigned_to_nat(0u);
x_319 = l_Array_empty___closed__1;
lean_inc(x_3);
x_320 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main(x_316, x_2, x_318, x_319, x_318, x_319, x_317, x_3, x_315);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_321, 3);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 4);
lean_inc(x_326);
x_327 = lean_ctor_get(x_321, 5);
lean_inc(x_327);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 x_328 = x_321;
} else {
 lean_dec_ref(x_321);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 6, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_323);
lean_ctor_set(x_329, 1, x_306);
lean_ctor_set(x_329, 2, x_324);
lean_ctor_set(x_329, 3, x_325);
lean_ctor_set(x_329, 4, x_326);
lean_ctor_set(x_329, 5, x_327);
x_330 = l_Lean_Meta_mkAppM___closed__1;
x_331 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_330, x_3, x_329);
lean_dec(x_3);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_322);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_335 = lean_ctor_get(x_320, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_320, 0);
lean_inc(x_336);
lean_dec(x_320);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_335, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_335, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_335, 5);
lean_inc(x_341);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 lean_ctor_release(x_335, 4);
 lean_ctor_release(x_335, 5);
 x_342 = x_335;
} else {
 lean_dec_ref(x_335);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 6, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_337);
lean_ctor_set(x_343, 1, x_306);
lean_ctor_set(x_343, 2, x_338);
lean_ctor_set(x_343, 3, x_339);
lean_ctor_set(x_343, 4, x_340);
lean_ctor_set(x_343, 5, x_341);
x_344 = l_Lean_Meta_mkAppM___closed__1;
x_345 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_344, x_3, x_343);
lean_dec(x_3);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
 lean_ctor_set_tag(x_348, 1);
}
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_349 = lean_ctor_get(x_313, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_313, 0);
lean_inc(x_350);
lean_dec(x_313);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_356 = x_349;
} else {
 lean_dec_ref(x_349);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 6, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_306);
lean_ctor_set(x_357, 2, x_352);
lean_ctor_set(x_357, 3, x_353);
lean_ctor_set(x_357, 4, x_354);
lean_ctor_set(x_357, 5, x_355);
x_358 = l_Lean_Meta_mkAppM___closed__1;
x_359 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_358, x_3, x_357);
lean_dec(x_3);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_350);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
}
}
}
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkAppM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_array_push(x_4, x_11);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppOptM");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments provided to");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_81 = lean_ctor_get(x_7, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_7, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_7, 2);
lean_inc(x_83);
x_84 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_85 = lean_array_get_size(x_4);
x_86 = lean_expr_instantiate_rev_range(x_82, x_5, x_85, x_4);
lean_dec(x_85);
lean_dec(x_82);
x_87 = lean_array_get_size(x_2);
x_88 = lean_nat_dec_lt(x_3, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_5);
lean_dec(x_3);
x_89 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
x_90 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_89, x_1, x_4, x_6, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_90;
}
else
{
lean_object* x_91; 
x_91 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; lean_object* x_93; 
x_92 = (uint8_t)((x_84 << 24) >> 61);
x_93 = lean_box(x_92);
if (lean_obj_tag(x_93) == 3)
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = 1;
lean_inc(x_8);
x_95 = l_Lean_Meta_mkFreshExprMVar(x_86, x_81, x_94, x_8, x_9);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_3, x_98);
lean_dec(x_3);
lean_inc(x_96);
x_100 = lean_array_push(x_4, x_96);
x_101 = l_Lean_Expr_mvarId_x21(x_96);
lean_dec(x_96);
x_102 = lean_array_push(x_6, x_101);
x_3 = x_99;
x_4 = x_100;
x_6 = x_102;
x_7 = x_83;
x_9 = x_97;
goto _start;
}
else
{
uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_93);
x_104 = 0;
lean_inc(x_8);
x_105 = l_Lean_Meta_mkFreshExprMVar(x_86, x_81, x_104, x_8, x_9);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_nat_add(x_3, x_108);
lean_dec(x_3);
x_110 = lean_array_push(x_4, x_106);
x_3 = x_109;
x_4 = x_110;
x_7 = x_83;
x_9 = x_107;
goto _start;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_81);
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
lean_dec(x_91);
lean_inc(x_8);
lean_inc(x_112);
x_113 = l_Lean_Meta_inferType(x_112, x_8, x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_8);
x_116 = l_Lean_Meta_isExprDefEq(x_86, x_114, x_8, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
lean_dec(x_83);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_116, 1);
x_121 = lean_ctor_get(x_116, 0);
lean_dec(x_121);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_8, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_8, 0);
lean_inc(x_125);
lean_dec(x_8);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_128, x_1);
lean_dec(x_4);
x_130 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_112);
lean_ctor_set(x_130, 2, x_127);
lean_ctor_set_tag(x_116, 1);
lean_ctor_set(x_116, 0, x_130);
return x_116;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_131 = lean_ctor_get(x_116, 1);
lean_inc(x_131);
lean_dec(x_116);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_8, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_8, 0);
lean_inc(x_135);
lean_dec(x_8);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_134);
lean_ctor_set(x_137, 3, x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_138, x_1);
lean_dec(x_4);
x_140 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_112);
lean_ctor_set(x_140, 2, x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_131);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_116, 1);
lean_inc(x_142);
lean_dec(x_116);
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_add(x_3, x_143);
lean_dec(x_3);
x_145 = lean_array_push(x_4, x_112);
x_3 = x_144;
x_4 = x_145;
x_7 = x_83;
x_9 = x_142;
goto _start;
}
}
else
{
uint8_t x_147; 
lean_dec(x_112);
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_116);
if (x_147 == 0)
{
return x_116;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_116, 0);
x_149 = lean_ctor_get(x_116, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_116);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_112);
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_113);
if (x_151 == 0)
{
return x_113;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_113, 0);
x_153 = lean_ctor_get(x_113, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_113);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
else
{
lean_object* x_155; 
x_155 = lean_box(0);
x_10 = x_155;
goto block_80;
}
block_80:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_4);
x_12 = lean_expr_instantiate_rev_range(x_7, x_5, x_11, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_8);
x_13 = l_Lean_Meta_whnfD(x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_isForall(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_11);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_eq(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_empty___closed__1;
x_22 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1(x_2, x_2, x_20, x_21);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
lean_dec(x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_30 = l_Lean_indentExpr(x_29);
x_31 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_MessageData_ofList___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_38 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_22, x_20, x_37);
lean_dec(x_22);
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
x_41 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_28);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_41);
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_13);
x_42 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
x_43 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_42, x_1, x_4, x_6, x_8, x_16);
lean_dec(x_6);
lean_dec(x_4);
return x_43;
}
}
else
{
lean_free_object(x_13);
x_5 = x_11;
x_7 = x_15;
x_9 = x_16;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
x_47 = l_Lean_Expr_isForall(x_45);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_45);
lean_dec(x_11);
x_48 = lean_array_get_size(x_2);
x_49 = lean_nat_dec_eq(x_3, x_48);
lean_dec(x_48);
lean_dec(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_6);
lean_dec(x_4);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_empty___closed__1;
x_52 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1(x_2, x_2, x_50, x_51);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 0);
lean_inc(x_56);
lean_dec(x_8);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_55);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_59, 0, x_1);
x_60 = l_Lean_indentExpr(x_59);
x_61 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_MessageData_ofList___closed__3;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8;
x_66 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_MessageData_coeOfArrayExpr___closed__2;
x_68 = l_Lean_MessageData_arrayExpr_toMessageData___main(x_52, x_50, x_67);
lean_dec(x_52);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
x_71 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_58);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_46);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2;
x_74 = l___private_Lean_Meta_AppBuilder_3__mkAppMFinal(x_73, x_1, x_4, x_6, x_8, x_46);
lean_dec(x_6);
lean_dec(x_4);
return x_74;
}
}
else
{
x_5 = x_11;
x_7 = x_45;
x_9 = x_46;
goto _start;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_13);
if (x_76 == 0)
{
return x_13;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_13, 0);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_13);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_mkAppOptM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_4, 4);
lean_inc(x_364);
x_365 = lean_ctor_get_uint8(x_364, sizeof(void*)*1);
lean_dec(x_364);
if (x_365 == 0)
{
uint8_t x_366; 
x_366 = 0;
x_5 = x_366;
x_6 = x_4;
goto block_363;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
x_367 = l_Lean_Meta_mkAppM___closed__1;
x_368 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_367, x_3, x_4);
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
lean_dec(x_368);
x_371 = lean_unbox(x_369);
lean_dec(x_369);
x_5 = x_371;
x_6 = x_370;
goto block_363;
}
block_363:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_12 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_12);
lean_inc(x_10);
x_13 = l_Lean_MetavarContext_incDepth(x_10);
lean_ctor_set(x_6, 1, x_13);
x_14 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_empty___closed__1;
x_21 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_17, x_2, x_19, x_20, x_19, x_20, x_18, x_3, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 4);
lean_inc(x_23);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_21, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 4);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_11);
lean_ctor_set(x_22, 1, x_10);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_11);
lean_ctor_set(x_22, 4, x_31);
lean_ctor_set(x_22, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 2);
x_34 = lean_ctor_get(x_22, 3);
x_35 = lean_ctor_get(x_22, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_37 = x_23;
} else {
 lean_dec_ref(x_23);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_11);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_21, 1, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_22, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_22, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 5);
lean_inc(x_44);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 x_45 = x_22;
} else {
 lean_dec_ref(x_22);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_23, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_47 = x_23;
} else {
 lean_dec_ref(x_23);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_45)) {
 x_49 = lean_alloc_ctor(0, 6, 0);
} else {
 x_49 = x_45;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_10);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_43);
lean_ctor_set(x_49, 4, x_48);
lean_ctor_set(x_49, 5, x_44);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 4);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_21, 1);
lean_dec(x_54);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_51, 4);
lean_dec(x_56);
x_57 = lean_ctor_get(x_51, 1);
lean_dec(x_57);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_11);
lean_ctor_set(x_51, 1, x_10);
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_11);
lean_ctor_set(x_51, 4, x_60);
lean_ctor_set(x_51, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 2);
x_63 = lean_ctor_get(x_51, 3);
x_64 = lean_ctor_get(x_51, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_51);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_11);
x_68 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_10);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_64);
lean_ctor_set(x_21, 1, x_68);
return x_21;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_21, 0);
lean_inc(x_69);
lean_dec(x_21);
x_70 = lean_ctor_get(x_51, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_51, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_51, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_51, 5);
lean_inc(x_73);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 lean_ctor_release(x_51, 3);
 lean_ctor_release(x_51, 4);
 lean_ctor_release(x_51, 5);
 x_74 = x_51;
} else {
 lean_dec_ref(x_51);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_52, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_76 = x_52;
} else {
 lean_dec_ref(x_52);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 1, 1);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_74)) {
 x_78 = lean_alloc_ctor(0, 6, 0);
} else {
 x_78 = x_74;
}
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_10);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set(x_78, 4, x_77);
lean_ctor_set(x_78, 5, x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_3);
x_80 = lean_ctor_get(x_14, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_80, 4);
lean_inc(x_81);
x_82 = !lean_is_exclusive(x_14);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_14, 1);
lean_dec(x_83);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_80, 4);
lean_dec(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_dec(x_86);
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_11);
lean_ctor_set(x_80, 1, x_10);
return x_14;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_81, 0);
lean_inc(x_88);
lean_dec(x_81);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_11);
lean_ctor_set(x_80, 4, x_89);
lean_ctor_set(x_80, 1, x_10);
return x_14;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 2);
x_92 = lean_ctor_get(x_80, 3);
x_93 = lean_ctor_get(x_80, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
x_94 = lean_ctor_get(x_81, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_95 = x_81;
} else {
 lean_dec_ref(x_81);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_11);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_10);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_96);
lean_ctor_set(x_97, 5, x_93);
lean_ctor_set(x_14, 1, x_97);
return x_14;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_98 = lean_ctor_get(x_14, 0);
lean_inc(x_98);
lean_dec(x_14);
x_99 = lean_ctor_get(x_80, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_80, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_80, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_80, 5);
lean_inc(x_102);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 lean_ctor_release(x_80, 5);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_81, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_105 = x_81;
} else {
 lean_dec_ref(x_81);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 1, 1);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_99);
lean_ctor_set(x_107, 1, x_10);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_101);
lean_ctor_set(x_107, 4, x_106);
lean_ctor_set(x_107, 5, x_102);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_ctor_get(x_6, 1);
x_110 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
lean_dec(x_8);
x_112 = 0;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
lean_inc(x_109);
x_114 = l_Lean_MetavarContext_incDepth(x_109);
lean_ctor_set(x_6, 4, x_113);
lean_ctor_set(x_6, 1, x_114);
x_115 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_6);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Array_empty___closed__1;
x_122 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_118, x_2, x_120, x_121, x_120, x_121, x_119, x_3, x_117);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 4);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_123, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 1, 1);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_127);
lean_ctor_set(x_135, 1, x_109);
lean_ctor_set(x_135, 2, x_128);
lean_ctor_set(x_135, 3, x_129);
lean_ctor_set(x_135, 4, x_134);
lean_ctor_set(x_135, 5, x_130);
if (lean_is_scalar(x_126)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_126;
}
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_137, 4);
lean_inc(x_138);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_140 = x_122;
} else {
 lean_dec_ref(x_122);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 2);
lean_inc(x_142);
x_143 = lean_ctor_get(x_137, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 lean_ctor_release(x_137, 5);
 x_145 = x_137;
} else {
 lean_dec_ref(x_137);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_138, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_147 = x_138;
} else {
 lean_dec_ref(x_138);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 1, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_145)) {
 x_149 = lean_alloc_ctor(0, 6, 0);
} else {
 x_149 = x_145;
}
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_109);
lean_ctor_set(x_149, 2, x_142);
lean_ctor_set(x_149, 3, x_143);
lean_ctor_set(x_149, 4, x_148);
lean_ctor_set(x_149, 5, x_144);
if (lean_is_scalar(x_140)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_140;
}
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_3);
x_151 = lean_ctor_get(x_115, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_115, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_154 = x_115;
} else {
 lean_dec_ref(x_115);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_151, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 5);
lean_inc(x_158);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 lean_ctor_release(x_151, 2);
 lean_ctor_release(x_151, 3);
 lean_ctor_release(x_151, 4);
 lean_ctor_release(x_151, 5);
 x_159 = x_151;
} else {
 lean_dec_ref(x_151);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_161 = x_152;
} else {
 lean_dec_ref(x_152);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(0, 1, 1);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_110);
if (lean_is_scalar(x_159)) {
 x_163 = lean_alloc_ctor(0, 6, 0);
} else {
 x_163 = x_159;
}
lean_ctor_set(x_163, 0, x_155);
lean_ctor_set(x_163, 1, x_109);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
lean_ctor_set(x_163, 4, x_162);
lean_ctor_set(x_163, 5, x_158);
if (lean_is_scalar(x_154)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_154;
}
lean_ctor_set(x_164, 0, x_153);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_ctor_get(x_6, 4);
x_166 = lean_ctor_get(x_6, 0);
x_167 = lean_ctor_get(x_6, 1);
x_168 = lean_ctor_get(x_6, 2);
x_169 = lean_ctor_get(x_6, 3);
x_170 = lean_ctor_get(x_6, 5);
lean_inc(x_170);
lean_inc(x_165);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_6);
x_171 = lean_ctor_get_uint8(x_165, sizeof(void*)*1);
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_173 = x_165;
} else {
 lean_dec_ref(x_165);
 x_173 = lean_box(0);
}
x_174 = 0;
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 1, 1);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
lean_inc(x_167);
x_176 = l_Lean_MetavarContext_incDepth(x_167);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_166);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_168);
lean_ctor_set(x_177, 3, x_169);
lean_ctor_set(x_177, 4, x_175);
lean_ctor_set(x_177, 5, x_170);
x_178 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_empty___closed__1;
x_185 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_181, x_2, x_183, x_184, x_183, x_184, x_182, x_3, x_180);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 4);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_189 = x_185;
} else {
 lean_dec_ref(x_185);
 x_189 = lean_box(0);
}
x_190 = lean_ctor_get(x_186, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_186, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_186, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 lean_ctor_release(x_186, 4);
 lean_ctor_release(x_186, 5);
 x_194 = x_186;
} else {
 lean_dec_ref(x_186);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_187, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_196 = x_187;
} else {
 lean_dec_ref(x_187);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 1, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_167);
lean_ctor_set(x_198, 2, x_191);
lean_ctor_set(x_198, 3, x_192);
lean_ctor_set(x_198, 4, x_197);
lean_ctor_set(x_198, 5, x_193);
if (lean_is_scalar(x_189)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_189;
}
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 4);
lean_inc(x_201);
x_202 = lean_ctor_get(x_185, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_203 = x_185;
} else {
 lean_dec_ref(x_185);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_200, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_200, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 5);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(0, 1, 1);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 6, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_204);
lean_ctor_set(x_212, 1, x_167);
lean_ctor_set(x_212, 2, x_205);
lean_ctor_set(x_212, 3, x_206);
lean_ctor_set(x_212, 4, x_211);
lean_ctor_set(x_212, 5, x_207);
if (lean_is_scalar(x_203)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_203;
}
lean_ctor_set(x_213, 0, x_202);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_3);
x_214 = lean_ctor_get(x_178, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_178, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_217 = x_178;
} else {
 lean_dec_ref(x_178);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 5);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 lean_ctor_release(x_214, 5);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_215, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 x_224 = x_215;
} else {
 lean_dec_ref(x_215);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 1, 1);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_171);
if (lean_is_scalar(x_222)) {
 x_226 = lean_alloc_ctor(0, 6, 0);
} else {
 x_226 = x_222;
}
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_167);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set(x_226, 4, x_225);
lean_ctor_set(x_226, 5, x_221);
if (lean_is_scalar(x_217)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_217;
}
lean_ctor_set(x_227, 0, x_216);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l___private_Lean_Util_Trace_3__getResetTraces___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__6___rarg(x_6);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 0);
lean_inc(x_230);
lean_dec(x_228);
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_229, 1);
lean_inc(x_232);
x_233 = l_Lean_MetavarContext_incDepth(x_232);
lean_ctor_set(x_229, 1, x_233);
x_234 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_229);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Array_empty___closed__1;
lean_inc(x_3);
x_241 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_237, x_2, x_239, x_240, x_239, x_240, x_238, x_3, x_236);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = !lean_is_exclusive(x_242);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = lean_ctor_get(x_242, 1);
lean_dec(x_245);
lean_ctor_set(x_242, 1, x_232);
x_246 = l_Lean_Meta_mkAppM___closed__1;
x_247 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_246, x_3, x_242);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_247, 0);
lean_dec(x_249);
lean_ctor_set(x_247, 0, x_243);
return x_247;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_250);
lean_dec(x_247);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_243);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_252 = lean_ctor_get(x_242, 0);
x_253 = lean_ctor_get(x_242, 2);
x_254 = lean_ctor_get(x_242, 3);
x_255 = lean_ctor_get(x_242, 4);
x_256 = lean_ctor_get(x_242, 5);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_242);
x_257 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_232);
lean_ctor_set(x_257, 2, x_253);
lean_ctor_set(x_257, 3, x_254);
lean_ctor_set(x_257, 4, x_255);
lean_ctor_set(x_257, 5, x_256);
x_258 = l_Lean_Meta_mkAppM___closed__1;
x_259 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_258, x_3, x_257);
lean_dec(x_3);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_243);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_241, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_241, 0);
lean_inc(x_264);
lean_dec(x_241);
x_265 = !lean_is_exclusive(x_263);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_266 = lean_ctor_get(x_263, 1);
lean_dec(x_266);
lean_ctor_set(x_263, 1, x_232);
x_267 = l_Lean_Meta_mkAppM___closed__1;
x_268 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_267, x_3, x_263);
lean_dec(x_3);
x_269 = !lean_is_exclusive(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_268, 0);
lean_dec(x_270);
lean_ctor_set_tag(x_268, 1);
lean_ctor_set(x_268, 0, x_264);
return x_268;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
lean_dec(x_268);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_273 = lean_ctor_get(x_263, 0);
x_274 = lean_ctor_get(x_263, 2);
x_275 = lean_ctor_get(x_263, 3);
x_276 = lean_ctor_get(x_263, 4);
x_277 = lean_ctor_get(x_263, 5);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_263);
x_278 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set(x_278, 1, x_232);
lean_ctor_set(x_278, 2, x_274);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set(x_278, 5, x_277);
x_279 = l_Lean_Meta_mkAppM___closed__1;
x_280 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_279, x_3, x_278);
lean_dec(x_3);
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
 lean_ctor_set_tag(x_283, 1);
}
lean_ctor_set(x_283, 0, x_264);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; 
x_284 = lean_ctor_get(x_234, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_234, 0);
lean_inc(x_285);
lean_dec(x_234);
x_286 = !lean_is_exclusive(x_284);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_287 = lean_ctor_get(x_284, 1);
lean_dec(x_287);
lean_ctor_set(x_284, 1, x_232);
x_288 = l_Lean_Meta_mkAppM___closed__1;
x_289 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_288, x_3, x_284);
lean_dec(x_3);
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_289, 0);
lean_dec(x_291);
lean_ctor_set_tag(x_289, 1);
lean_ctor_set(x_289, 0, x_285);
return x_289;
}
else
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec(x_289);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_285);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_284, 0);
x_295 = lean_ctor_get(x_284, 2);
x_296 = lean_ctor_get(x_284, 3);
x_297 = lean_ctor_get(x_284, 4);
x_298 = lean_ctor_get(x_284, 5);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_284);
x_299 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_299, 0, x_294);
lean_ctor_set(x_299, 1, x_232);
lean_ctor_set(x_299, 2, x_295);
lean_ctor_set(x_299, 3, x_296);
lean_ctor_set(x_299, 4, x_297);
lean_ctor_set(x_299, 5, x_298);
x_300 = l_Lean_Meta_mkAppM___closed__1;
x_301 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_300, x_3, x_299);
lean_dec(x_3);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
 lean_ctor_set_tag(x_304, 1);
}
lean_ctor_set(x_304, 0, x_285);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_229, 0);
x_306 = lean_ctor_get(x_229, 1);
x_307 = lean_ctor_get(x_229, 2);
x_308 = lean_ctor_get(x_229, 3);
x_309 = lean_ctor_get(x_229, 4);
x_310 = lean_ctor_get(x_229, 5);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_229);
lean_inc(x_306);
x_311 = l_Lean_MetavarContext_incDepth(x_306);
x_312 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_312, 0, x_305);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_312, 2, x_307);
lean_ctor_set(x_312, 3, x_308);
lean_ctor_set(x_312, 4, x_309);
lean_ctor_set(x_312, 5, x_310);
x_313 = l___private_Lean_Meta_AppBuilder_5__mkFun(x_1, x_3, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_unsigned_to_nat(0u);
x_319 = l_Array_empty___closed__1;
lean_inc(x_3);
x_320 = l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main(x_316, x_2, x_318, x_319, x_318, x_319, x_317, x_3, x_315);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 0);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_ctor_get(x_321, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_321, 3);
lean_inc(x_325);
x_326 = lean_ctor_get(x_321, 4);
lean_inc(x_326);
x_327 = lean_ctor_get(x_321, 5);
lean_inc(x_327);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 lean_ctor_release(x_321, 2);
 lean_ctor_release(x_321, 3);
 lean_ctor_release(x_321, 4);
 lean_ctor_release(x_321, 5);
 x_328 = x_321;
} else {
 lean_dec_ref(x_321);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(0, 6, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_323);
lean_ctor_set(x_329, 1, x_306);
lean_ctor_set(x_329, 2, x_324);
lean_ctor_set(x_329, 3, x_325);
lean_ctor_set(x_329, 4, x_326);
lean_ctor_set(x_329, 5, x_327);
x_330 = l_Lean_Meta_mkAppM___closed__1;
x_331 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_330, x_3, x_329);
lean_dec(x_3);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_333 = x_331;
} else {
 lean_dec_ref(x_331);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_322);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_335 = lean_ctor_get(x_320, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_320, 0);
lean_inc(x_336);
lean_dec(x_320);
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_335, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_335, 3);
lean_inc(x_339);
x_340 = lean_ctor_get(x_335, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_335, 5);
lean_inc(x_341);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 lean_ctor_release(x_335, 1);
 lean_ctor_release(x_335, 2);
 lean_ctor_release(x_335, 3);
 lean_ctor_release(x_335, 4);
 lean_ctor_release(x_335, 5);
 x_342 = x_335;
} else {
 lean_dec_ref(x_335);
 x_342 = lean_box(0);
}
if (lean_is_scalar(x_342)) {
 x_343 = lean_alloc_ctor(0, 6, 0);
} else {
 x_343 = x_342;
}
lean_ctor_set(x_343, 0, x_337);
lean_ctor_set(x_343, 1, x_306);
lean_ctor_set(x_343, 2, x_338);
lean_ctor_set(x_343, 3, x_339);
lean_ctor_set(x_343, 4, x_340);
lean_ctor_set(x_343, 5, x_341);
x_344 = l_Lean_Meta_mkAppM___closed__1;
x_345 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_344, x_3, x_343);
lean_dec(x_3);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_347 = x_345;
} else {
 lean_dec_ref(x_345);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
 lean_ctor_set_tag(x_348, 1);
}
lean_ctor_set(x_348, 0, x_336);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_349 = lean_ctor_get(x_313, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_313, 0);
lean_inc(x_350);
lean_dec(x_313);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_356 = x_349;
} else {
 lean_dec_ref(x_349);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(0, 6, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_306);
lean_ctor_set(x_357, 2, x_352);
lean_ctor_set(x_357, 3, x_353);
lean_ctor_set(x_357, 4, x_354);
lean_ctor_set(x_357, 5, x_355);
x_358 = l_Lean_Meta_mkAppM___closed__1;
x_359 = l___private_Lean_Util_Trace_2__addNode___at___private_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_230, x_358, x_3, x_357);
lean_dec(x_3);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_361 = x_359;
} else {
 lean_dec_ref(x_359);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_350);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
}
}
}
lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkAppOptM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ndrec");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqNDRec___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid motive");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqNDRec___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkEqNDRec___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqNDRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_mkEqRefl___closed__2;
x_7 = l_Lean_Expr_isAppOf(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_AppBuilder_1__infer(x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_eq_x3f___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_3, x_10);
x_22 = l_Lean_Meta_mkEqSymm___closed__5;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_mkEqNDRec___closed__2;
x_25 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_8);
x_26 = l_Lean_Expr_appFn_x21(x_10);
x_27 = l_Lean_Expr_appFn_x21(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_30 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_28);
x_31 = l_Lean_Meta_getLevel(x_28, x_4, x_11);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_4);
lean_inc(x_1);
x_35 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
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
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_36, 2);
lean_inc(x_54);
lean_dec(x_36);
if (lean_obj_tag(x_54) == 3)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_38);
lean_dec(x_4);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Meta_mkEqNDRec___closed__2;
x_60 = l_Lean_mkConst(x_59, x_58);
x_61 = l_Lean_Meta_mkEqNDRec___closed__6;
x_62 = lean_array_push(x_61, x_28);
x_63 = lean_array_push(x_62, x_29);
x_64 = lean_array_push(x_63, x_1);
x_65 = lean_array_push(x_64, x_2);
x_66 = lean_array_push(x_65, x_30);
x_67 = lean_array_push(x_66, x_3);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_67, x_67, x_68, x_60);
lean_dec(x_67);
lean_ctor_set(x_31, 1, x_37);
lean_ctor_set(x_31, 0, x_69);
return x_31;
}
else
{
lean_object* x_70; 
lean_dec(x_54);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
x_39 = x_70;
goto block_53;
}
}
else
{
lean_object* x_71; 
lean_dec(x_36);
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
x_39 = x_71;
goto block_53;
}
block_53:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 0);
lean_inc(x_43);
lean_dec(x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l_Lean_indentExpr(x_46);
x_48 = l_Lean_Meta_mkEqNDRec___closed__5;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_mkEqNDRec___closed__2;
x_51 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_45);
if (lean_is_scalar(x_38)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_38;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_37);
return x_52;
}
}
else
{
uint8_t x_72; 
lean_free_object(x_31);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_35);
if (x_72 == 0)
{
return x_35;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_35, 0);
x_74 = lean_ctor_get(x_35, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_35);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_31, 0);
x_77 = lean_ctor_get(x_31, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_31);
lean_inc(x_4);
lean_inc(x_1);
x_78 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_obj_tag(x_79) == 7)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_79, 2);
lean_inc(x_97);
lean_dec(x_79);
if (lean_obj_tag(x_97) == 3)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_81);
lean_dec(x_4);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_76);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_mkEqNDRec___closed__2;
x_103 = l_Lean_mkConst(x_102, x_101);
x_104 = l_Lean_Meta_mkEqNDRec___closed__6;
x_105 = lean_array_push(x_104, x_28);
x_106 = lean_array_push(x_105, x_29);
x_107 = lean_array_push(x_106, x_1);
x_108 = lean_array_push(x_107, x_2);
x_109 = lean_array_push(x_108, x_30);
x_110 = lean_array_push(x_109, x_3);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_110, x_110, x_111, x_103);
lean_dec(x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_80);
return x_113;
}
else
{
lean_object* x_114; 
lean_dec(x_97);
lean_dec(x_76);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_box(0);
x_82 = x_114;
goto block_96;
}
}
else
{
lean_object* x_115; 
lean_dec(x_79);
lean_dec(x_76);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_115 = lean_box(0);
x_82 = x_115;
goto block_96;
}
block_96:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_4, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_4, 0);
lean_inc(x_86);
lean_dec(x_4);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set(x_88, 3, x_87);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_1);
x_90 = l_Lean_indentExpr(x_89);
x_91 = l_Lean_Meta_mkEqNDRec___closed__5;
x_92 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Meta_mkEqNDRec___closed__2;
x_94 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_88);
if (lean_is_scalar(x_81)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_81;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_80);
return x_95;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_76);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_78, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_78, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_118 = x_78;
} else {
 lean_dec_ref(x_78);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_31);
if (x_120 == 0)
{
return x_31;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_31, 0);
x_122 = lean_ctor_get(x_31, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_31);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_124 = lean_ctor_get(x_8, 0);
x_125 = lean_ctor_get(x_8, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_8);
x_126 = l_Lean_Expr_eq_x3f___closed__2;
x_127 = lean_unsigned_to_nat(3u);
x_128 = l_Lean_Expr_isAppOfArity___main(x_124, x_126, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_4, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_4, 0);
lean_inc(x_132);
lean_dec(x_4);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_130);
lean_ctor_set(x_134, 2, x_131);
lean_ctor_set(x_134, 3, x_133);
x_135 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_3, x_124);
x_136 = l_Lean_Meta_mkEqSymm___closed__5;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Meta_mkEqNDRec___closed__2;
x_139 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
lean_ctor_set(x_139, 2, x_134);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_125);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = l_Lean_Expr_appFn_x21(x_124);
x_142 = l_Lean_Expr_appFn_x21(x_141);
x_143 = l_Lean_Expr_appArg_x21(x_142);
lean_dec(x_142);
x_144 = l_Lean_Expr_appArg_x21(x_141);
lean_dec(x_141);
x_145 = l_Lean_Expr_appArg_x21(x_124);
lean_dec(x_124);
lean_inc(x_4);
lean_inc(x_143);
x_146 = l_Lean_Meta_getLevel(x_143, x_4, x_125);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_1);
x_150 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
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
if (lean_obj_tag(x_151) == 7)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_151, 2);
lean_inc(x_169);
lean_dec(x_151);
if (lean_obj_tag(x_169) == 3)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_153);
lean_dec(x_4);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_147);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_Meta_mkEqNDRec___closed__2;
x_175 = l_Lean_mkConst(x_174, x_173);
x_176 = l_Lean_Meta_mkEqNDRec___closed__6;
x_177 = lean_array_push(x_176, x_143);
x_178 = lean_array_push(x_177, x_144);
x_179 = lean_array_push(x_178, x_1);
x_180 = lean_array_push(x_179, x_2);
x_181 = lean_array_push(x_180, x_145);
x_182 = lean_array_push(x_181, x_3);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_182, x_182, x_183, x_175);
lean_dec(x_182);
if (lean_is_scalar(x_149)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_149;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_152);
return x_185;
}
else
{
lean_object* x_186; 
lean_dec(x_169);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_box(0);
x_154 = x_186;
goto block_168;
}
}
else
{
lean_object* x_187; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_3);
lean_dec(x_2);
x_187 = lean_box(0);
x_154 = x_187;
goto block_168;
}
block_168:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_154);
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_4, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_4, 0);
lean_inc(x_158);
lean_dec(x_4);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_156);
lean_ctor_set(x_160, 2, x_157);
lean_ctor_set(x_160, 3, x_159);
x_161 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_161, 0, x_1);
x_162 = l_Lean_indentExpr(x_161);
x_163 = l_Lean_Meta_mkEqNDRec___closed__5;
x_164 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_Meta_mkEqNDRec___closed__2;
x_166 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
lean_ctor_set(x_166, 2, x_160);
if (lean_is_scalar(x_153)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_153;
 lean_ctor_set_tag(x_167, 1);
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_152);
return x_167;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_150, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_150, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_190 = x_150;
} else {
 lean_dec_ref(x_150);
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
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_146, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_146, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_194 = x_146;
} else {
 lean_dec_ref(x_146);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_8);
if (x_196 == 0)
{
return x_8;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_8, 0);
x_198 = lean_ctor_get(x_8, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_8);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_2);
lean_ctor_set(x_200, 1, x_5);
return x_200;
}
}
}
lean_object* _init_l_Lean_Meta_mkEqRec___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_mkRecFor___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Meta_mkEqRefl___closed__2;
x_7 = l_Lean_Expr_isAppOf(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_4);
lean_inc(x_3);
x_8 = l___private_Lean_Meta_AppBuilder_1__infer(x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_eq_x3f___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_3);
x_22 = l_Lean_indentExpr(x_21);
x_23 = l_Lean_Meta_mkEqSymm___closed__5;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_mkEqRec___closed__1;
x_26 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_8);
x_27 = l_Lean_Expr_appFn_x21(x_10);
x_28 = l_Lean_Expr_appFn_x21(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_28);
lean_dec(x_28);
x_30 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_31 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_4);
lean_inc(x_29);
x_32 = l_Lean_Meta_getLevel(x_29, x_4, x_11);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_4);
lean_inc(x_1);
x_36 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
if (lean_obj_tag(x_37) == 7)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_37, 2);
lean_inc(x_55);
lean_dec(x_37);
if (lean_obj_tag(x_55) == 7)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 3)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_39);
lean_dec(x_4);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_34);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_mkEqRec___closed__1;
x_62 = l_Lean_mkConst(x_61, x_60);
x_63 = l_Lean_Meta_mkEqNDRec___closed__6;
x_64 = lean_array_push(x_63, x_29);
x_65 = lean_array_push(x_64, x_30);
x_66 = lean_array_push(x_65, x_1);
x_67 = lean_array_push(x_66, x_2);
x_68 = lean_array_push(x_67, x_31);
x_69 = lean_array_push(x_68, x_3);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_69, x_69, x_70, x_62);
lean_dec(x_69);
lean_ctor_set(x_32, 1, x_38);
lean_ctor_set(x_32, 0, x_71);
return x_32;
}
else
{
lean_object* x_72; 
lean_dec(x_56);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(0);
x_40 = x_72;
goto block_54;
}
}
else
{
lean_object* x_73; 
lean_dec(x_55);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
x_40 = x_73;
goto block_54;
}
}
else
{
lean_object* x_74; 
lean_dec(x_37);
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_40 = x_74;
goto block_54;
}
block_54:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_40);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec(x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_43);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = l_Lean_indentExpr(x_47);
x_49 = l_Lean_Meta_mkEqNDRec___closed__5;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Meta_mkEqRec___closed__1;
x_52 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set(x_52, 2, x_46);
if (lean_is_scalar(x_39)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_39;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
}
else
{
uint8_t x_75; 
lean_free_object(x_32);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_36);
if (x_75 == 0)
{
return x_36;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_36, 0);
x_77 = lean_ctor_get(x_36, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_36);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_32, 0);
x_80 = lean_ctor_get(x_32, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_32);
lean_inc(x_4);
lean_inc(x_1);
x_81 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_obj_tag(x_82) == 7)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_82, 2);
lean_inc(x_100);
lean_dec(x_82);
if (lean_obj_tag(x_100) == 7)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 3)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_84);
lean_dec(x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_79);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Meta_mkEqRec___closed__1;
x_107 = l_Lean_mkConst(x_106, x_105);
x_108 = l_Lean_Meta_mkEqNDRec___closed__6;
x_109 = lean_array_push(x_108, x_29);
x_110 = lean_array_push(x_109, x_30);
x_111 = lean_array_push(x_110, x_1);
x_112 = lean_array_push(x_111, x_2);
x_113 = lean_array_push(x_112, x_31);
x_114 = lean_array_push(x_113, x_3);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_114, x_114, x_115, x_107);
lean_dec(x_114);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_83);
return x_117;
}
else
{
lean_object* x_118; 
lean_dec(x_101);
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_box(0);
x_85 = x_118;
goto block_99;
}
}
else
{
lean_object* x_119; 
lean_dec(x_100);
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_box(0);
x_85 = x_119;
goto block_99;
}
}
else
{
lean_object* x_120; 
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_box(0);
x_85 = x_120;
goto block_99;
}
block_99:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_4, 0);
lean_inc(x_89);
lean_dec(x_4);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_88);
lean_ctor_set(x_91, 3, x_90);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_1);
x_93 = l_Lean_indentExpr(x_92);
x_94 = l_Lean_Meta_mkEqNDRec___closed__5;
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Meta_mkEqRec___closed__1;
x_97 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_91);
if (lean_is_scalar(x_84)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_84;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_83);
return x_98;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_79);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_81, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_81, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_123 = x_81;
} else {
 lean_dec_ref(x_81);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_32);
if (x_125 == 0)
{
return x_32;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_32, 0);
x_127 = lean_ctor_get(x_32, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_32);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
x_131 = l_Lean_Expr_eq_x3f___closed__2;
x_132 = lean_unsigned_to_nat(3u);
x_133 = l_Lean_Expr_isAppOfArity___main(x_129, x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_129);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_4, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_4, 0);
lean_inc(x_137);
lean_dec(x_4);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_138);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_3);
x_141 = l_Lean_indentExpr(x_140);
x_142 = l_Lean_Meta_mkEqSymm___closed__5;
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Meta_mkEqRec___closed__1;
x_145 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_145, 2, x_139);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_130);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = l_Lean_Expr_appFn_x21(x_129);
x_148 = l_Lean_Expr_appFn_x21(x_147);
x_149 = l_Lean_Expr_appArg_x21(x_148);
lean_dec(x_148);
x_150 = l_Lean_Expr_appArg_x21(x_147);
lean_dec(x_147);
x_151 = l_Lean_Expr_appArg_x21(x_129);
lean_dec(x_129);
lean_inc(x_4);
lean_inc(x_149);
x_152 = l_Lean_Meta_getLevel(x_149, x_4, x_130);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_1);
x_156 = l___private_Lean_Meta_AppBuilder_1__infer(x_1, x_4, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_obj_tag(x_157) == 7)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_157, 2);
lean_inc(x_175);
lean_dec(x_157);
if (lean_obj_tag(x_175) == 7)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 2);
lean_inc(x_176);
lean_dec(x_175);
if (lean_obj_tag(x_176) == 3)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_159);
lean_dec(x_4);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_153);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_Meta_mkEqRec___closed__1;
x_182 = l_Lean_mkConst(x_181, x_180);
x_183 = l_Lean_Meta_mkEqNDRec___closed__6;
x_184 = lean_array_push(x_183, x_149);
x_185 = lean_array_push(x_184, x_150);
x_186 = lean_array_push(x_185, x_1);
x_187 = lean_array_push(x_186, x_2);
x_188 = lean_array_push(x_187, x_151);
x_189 = lean_array_push(x_188, x_3);
x_190 = lean_unsigned_to_nat(0u);
x_191 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_189, x_189, x_190, x_182);
lean_dec(x_189);
if (lean_is_scalar(x_155)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_155;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_158);
return x_192;
}
else
{
lean_object* x_193; 
lean_dec(x_176);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_3);
lean_dec(x_2);
x_193 = lean_box(0);
x_160 = x_193;
goto block_174;
}
}
else
{
lean_object* x_194; 
lean_dec(x_175);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_3);
lean_dec(x_2);
x_194 = lean_box(0);
x_160 = x_194;
goto block_174;
}
}
else
{
lean_object* x_195; 
lean_dec(x_157);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_3);
lean_dec(x_2);
x_195 = lean_box(0);
x_160 = x_195;
goto block_174;
}
block_174:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_160);
x_161 = lean_ctor_get(x_158, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_4, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_4, 0);
lean_inc(x_164);
lean_dec(x_4);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_162);
lean_ctor_set(x_166, 2, x_163);
lean_ctor_set(x_166, 3, x_165);
x_167 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_167, 0, x_1);
x_168 = l_Lean_indentExpr(x_167);
x_169 = l_Lean_Meta_mkEqNDRec___closed__5;
x_170 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
x_171 = l_Lean_Meta_mkEqRec___closed__1;
x_172 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_166);
if (lean_is_scalar(x_159)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_159;
 lean_ctor_set_tag(x_173, 1);
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_158);
return x_173;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_156, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_156, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_198 = x_156;
} else {
 lean_dec_ref(x_156);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_152, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_152, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_202 = x_152;
} else {
 lean_dec_ref(x_152);
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
uint8_t x_204; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_8);
if (x_204 == 0)
{
return x_8;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_8, 0);
x_206 = lean_ctor_get(x_8, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_8);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_2);
lean_ctor_set(x_208, 1, x_5);
return x_208;
}
}
}
lean_object* _init_l_Lean_Meta_mkEqMP___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mp");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqMP___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqMP___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqMP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Meta_mkEqMP___closed__2;
x_9 = l_Lean_Meta_mkAppM(x_8, x_7, x_3, x_4);
lean_dec(x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Meta_mkEqMPR___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mpr");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqMPR___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqMPR___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqMPR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Meta_mkEqMPR___closed__2;
x_9 = l_Lean_Meta_mkAppM(x_8, x_7, x_3, x_4);
lean_dec(x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("noConfusion");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkNoConfusion___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive type expected");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkNoConfusion___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkNoConfusion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Meta_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf(x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_eq_x3f___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity___main(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_10);
x_22 = l_Lean_Meta_mkNoConfusion___closed__5;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_mkNoConfusion___closed__2;
x_25 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_8);
x_26 = l_Lean_Expr_appFn_x21(x_10);
x_27 = l_Lean_Expr_appFn_x21(x_26);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_26);
lean_dec(x_26);
x_30 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
lean_inc(x_3);
x_31 = l_Lean_Meta_whnf(x_28, x_3, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_50; lean_object* x_51; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_50 = lean_ctor_get(x_33, 0);
lean_inc(x_50);
x_51 = l_Lean_Expr_getAppFn___main(x_32);
if (lean_obj_tag(x_51) == 4)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_environment_find(x_50, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
x_35 = x_55;
goto block_49;
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 5)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_34);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_1);
x_58 = l_Lean_Meta_getLevel(x_1, x_3, x_33);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Meta_mkNoConfusion___closed__1;
x_64 = lean_name_mk_string(x_62, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_53);
x_66 = l_Lean_mkConst(x_64, x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_Expr_getAppNumArgsAux___main(x_32, x_67);
x_69 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_68);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_68, x_71);
lean_dec(x_68);
x_73 = l___private_Lean_Expr_3__getAppArgsAux___main(x_32, x_70, x_72);
x_74 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_75 = lean_array_push(x_74, x_1);
x_76 = lean_array_push(x_75, x_29);
x_77 = lean_array_push(x_76, x_30);
x_78 = lean_array_push(x_77, x_2);
x_79 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_78, x_78, x_67, x_73);
lean_dec(x_78);
x_80 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_79, x_79, x_67, x_66);
lean_dec(x_79);
lean_ctor_set(x_58, 0, x_80);
return x_58;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_81 = lean_ctor_get(x_58, 0);
x_82 = lean_ctor_get(x_58, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_58);
x_83 = lean_ctor_get(x_57, 0);
lean_inc(x_83);
lean_dec(x_57);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Meta_mkNoConfusion___closed__1;
x_86 = lean_name_mk_string(x_84, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_53);
x_88 = l_Lean_mkConst(x_86, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Expr_getAppNumArgsAux___main(x_32, x_89);
x_91 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_90);
x_92 = lean_mk_array(x_90, x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_sub(x_90, x_93);
lean_dec(x_90);
x_95 = l___private_Lean_Expr_3__getAppArgsAux___main(x_32, x_92, x_94);
x_96 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_97 = lean_array_push(x_96, x_1);
x_98 = lean_array_push(x_97, x_29);
x_99 = lean_array_push(x_98, x_30);
x_100 = lean_array_push(x_99, x_2);
x_101 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_100, x_100, x_89, x_95);
lean_dec(x_100);
x_102 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_101, x_101, x_89, x_88);
lean_dec(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_82);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_57);
lean_dec(x_53);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_58);
if (x_104 == 0)
{
return x_58;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_58, 0);
x_106 = lean_ctor_get(x_58, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_58);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_box(0);
x_35 = x_108;
goto block_49;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
x_35 = x_109;
goto block_49;
}
block_49:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_32);
x_43 = l_Lean_indentExpr(x_42);
x_44 = l_Lean_Meta_mkNoConfusion___closed__8;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Meta_mkNoConfusion___closed__2;
x_47 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_41);
if (lean_is_scalar(x_34)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_34;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
return x_48;
}
}
else
{
uint8_t x_110; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_31);
if (x_110 == 0)
{
return x_31;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_31, 0);
x_112 = lean_ctor_get(x_31, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_31);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_8, 0);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_8);
x_116 = l_Lean_Expr_eq_x3f___closed__2;
x_117 = lean_unsigned_to_nat(3u);
x_118 = l_Lean_Expr_isAppOfArity___main(x_114, x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_1);
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_3, 0);
lean_inc(x_122);
lean_dec(x_3);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_124, 0, x_119);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_123);
x_125 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_2, x_114);
x_126 = l_Lean_Meta_mkNoConfusion___closed__5;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
x_128 = l_Lean_Meta_mkNoConfusion___closed__2;
x_129 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_124);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_115);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = l_Lean_Expr_appFn_x21(x_114);
x_132 = l_Lean_Expr_appFn_x21(x_131);
x_133 = l_Lean_Expr_appArg_x21(x_132);
lean_dec(x_132);
x_134 = l_Lean_Expr_appArg_x21(x_131);
lean_dec(x_131);
x_135 = l_Lean_Expr_appArg_x21(x_114);
lean_dec(x_114);
lean_inc(x_3);
x_136 = l_Lean_Meta_whnf(x_133, x_3, x_115);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_155; lean_object* x_156; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_155 = lean_ctor_get(x_138, 0);
lean_inc(x_155);
x_156 = l_Lean_Expr_getAppFn___main(x_137);
if (lean_obj_tag(x_156) == 4)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_environment_find(x_155, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; 
lean_dec(x_158);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_box(0);
x_140 = x_160;
goto block_154;
}
else
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_159, 0);
lean_inc(x_161);
lean_dec(x_159);
if (lean_obj_tag(x_161) == 5)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_139);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_1);
x_163 = l_Lean_Meta_getLevel(x_1, x_3, x_138);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_162, 0);
lean_inc(x_167);
lean_dec(x_162);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec(x_167);
x_169 = l_Lean_Meta_mkNoConfusion___closed__1;
x_170 = lean_name_mk_string(x_168, x_169);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_164);
lean_ctor_set(x_171, 1, x_158);
x_172 = l_Lean_mkConst(x_170, x_171);
x_173 = lean_unsigned_to_nat(0u);
x_174 = l_Lean_Expr_getAppNumArgsAux___main(x_137, x_173);
x_175 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_174);
x_176 = lean_mk_array(x_174, x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_sub(x_174, x_177);
lean_dec(x_174);
x_179 = l___private_Lean_Expr_3__getAppArgsAux___main(x_137, x_176, x_178);
x_180 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_181 = lean_array_push(x_180, x_1);
x_182 = lean_array_push(x_181, x_134);
x_183 = lean_array_push(x_182, x_135);
x_184 = lean_array_push(x_183, x_2);
x_185 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_184, x_184, x_173, x_179);
lean_dec(x_184);
x_186 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_185, x_185, x_173, x_172);
lean_dec(x_185);
if (lean_is_scalar(x_166)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_166;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_165);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_163, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_163, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_190 = x_163;
} else {
 lean_dec_ref(x_163);
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
else
{
lean_object* x_192; 
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_box(0);
x_140 = x_192;
goto block_154;
}
}
}
else
{
lean_object* x_193; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_box(0);
x_140 = x_193;
goto block_154;
}
block_154:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_140);
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_3, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_3, 0);
lean_inc(x_144);
lean_dec(x_3);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_142);
lean_ctor_set(x_146, 2, x_143);
lean_ctor_set(x_146, 3, x_145);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_137);
x_148 = l_Lean_indentExpr(x_147);
x_149 = l_Lean_Meta_mkNoConfusion___closed__8;
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_Meta_mkNoConfusion___closed__2;
x_152 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_146);
if (lean_is_scalar(x_139)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_139;
 lean_ctor_set_tag(x_153, 1);
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_138);
return x_153;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_136, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_136, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_196 = x_136;
} else {
 lean_dec_ref(x_136);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_8);
if (x_198 == 0)
{
return x_8;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_8, 0);
x_200 = lean_ctor_get(x_8, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_8);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_5);
if (x_202 == 0)
{
return x_5;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_5, 0);
x_204 = lean_ctor_get(x_5, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_5);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkPure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasPure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkPure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkPure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkPure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pure");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkPure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkPure___closed__2;
x_2 = l_Lean_Meta_mkPure___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkPure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_array_push(x_10, x_6);
x_12 = lean_array_push(x_11, x_7);
x_13 = l_Lean_Meta_mkPure___closed__4;
x_14 = l_Lean_Meta_mkAppOptM(x_13, x_12, x_3, x_4);
lean_dec(x_12);
return x_14;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_5, x_6);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_4);
x_14 = l_Lean_isSubobjectField_x3f(x_4, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_1);
x_20 = l_Lean_Meta_mkProjection___main(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_2);
x_23 = l_Lean_Meta_mkProjection___main(x_21, x_2, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_14, 0, x_25);
lean_ctor_set(x_23, 0, x_14);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
lean_ctor_set(x_14, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_14);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_6 = x_31;
x_8 = x_29;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_1);
x_37 = l_Lean_Meta_mkProjection___main(x_1, x_13, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_7);
lean_inc(x_2);
x_40 = l_Lean_Meta_mkProjection___main(x_38, x_2, x_7, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_6, x_47);
lean_dec(x_6);
x_6 = x_48;
x_8 = x_46;
goto _start;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
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
}
}
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkProjectionn");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkProjection___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getStructureCtor___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field name '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' for");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_mkProjection___main___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkProjection___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_3);
x_9 = l_Lean_Meta_whnf(x_7, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_27; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_27 = l_Lean_Expr_getAppFn___main(x_10);
if (lean_obj_tag(x_27) == 4)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_12);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_28);
lean_inc(x_30);
x_32 = l_Lean_isStructureLike(x_30, x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
lean_dec(x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_33);
lean_ctor_set(x_36, 3, x_35);
x_37 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_38 = l_Lean_Meta_mkProjection___main___closed__4;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Meta_mkProjection___main___closed__2;
x_41 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_41);
return x_5;
}
else
{
lean_object* x_42; 
lean_dec(x_31);
lean_inc(x_2);
lean_inc(x_28);
lean_inc(x_30);
x_42 = l_Lean_getProjFnForField_x3f(x_30, x_28, x_2);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_29);
lean_free_object(x_5);
lean_inc(x_28);
lean_inc(x_30);
x_43 = l_Lean_getStructureFields(x_30, x_28);
x_44 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1(x_1, x_2, x_28, x_30, x_43, x_44, x_3, x_11);
lean_dec(x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
lean_dec(x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_54);
x_56 = l_Lean_Name_toString___closed__1;
x_57 = l_Lean_Name_toStringWithSep___main(x_56, x_2);
x_58 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_Meta_mkProjection___main___closed__7;
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Meta_mkProjection___main___closed__10;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Meta_mkProjection___main___closed__2;
x_67 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_67, 2, x_55);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_67);
return x_45;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_dec(x_45);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
lean_dec(x_3);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_73);
x_75 = l_Lean_Name_toString___closed__1;
x_76 = l_Lean_Name_toStringWithSep___main(x_75, x_2);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_Meta_mkProjection___main___closed__7;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Meta_mkProjection___main___closed__10;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_mkProjection___main___closed__2;
x_86 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_68);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_45);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_45, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
lean_dec(x_46);
lean_ctor_set(x_45, 0, x_90);
return x_45;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_45, 1);
lean_inc(x_91);
lean_dec(x_45);
x_92 = lean_ctor_get(x_46, 0);
lean_inc(x_92);
lean_dec(x_46);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_45);
if (x_94 == 0)
{
return x_45;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_45, 0);
x_96 = lean_ctor_get(x_45, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_45);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_42, 0);
lean_inc(x_98);
lean_dec(x_42);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Lean_Expr_getAppNumArgsAux___main(x_10, x_99);
x_101 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_100);
x_102 = lean_mk_array(x_100, x_101);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_sub(x_100, x_103);
lean_dec(x_100);
x_105 = l___private_Lean_Expr_3__getAppArgsAux___main(x_10, x_102, x_104);
x_106 = l_Lean_mkConst(x_98, x_29);
x_107 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_105, x_105, x_99, x_106);
lean_dec(x_105);
x_108 = l_Lean_mkApp(x_107, x_1);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_108);
return x_5;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_27);
lean_free_object(x_5);
lean_dec(x_2);
x_109 = lean_box(0);
x_13 = x_109;
goto block_26;
}
block_26:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_10);
x_21 = l_Lean_Meta_mkProjection___main___closed__4;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_mkProjection___main___closed__2;
x_24 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_19);
if (lean_is_scalar(x_12)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_12;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
else
{
uint8_t x_110; 
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_9);
if (x_110 == 0)
{
return x_9;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_9, 0);
x_112 = lean_ctor_get(x_9, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_9);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_ctor_get(x_5, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_5);
lean_inc(x_3);
x_116 = l_Lean_Meta_whnf(x_114, x_3, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_134; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_134 = l_Lean_Expr_getAppFn___main(x_117);
if (lean_obj_tag(x_134) == 4)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_119);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_118, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_118, 1);
lean_inc(x_138);
lean_inc(x_135);
lean_inc(x_137);
x_139 = l_Lean_isStructureLike(x_137, x_135);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
x_140 = lean_ctor_get(x_3, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 0);
lean_inc(x_141);
lean_dec(x_3);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_137);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_140);
lean_ctor_set(x_143, 3, x_142);
x_144 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_117);
x_145 = l_Lean_Meta_mkProjection___main___closed__4;
x_146 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = l_Lean_Meta_mkProjection___main___closed__2;
x_148 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_143);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_118);
return x_149;
}
else
{
lean_object* x_150; 
lean_dec(x_138);
lean_inc(x_2);
lean_inc(x_135);
lean_inc(x_137);
x_150 = l_Lean_getProjFnForField_x3f(x_137, x_135, x_2);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_136);
lean_inc(x_135);
lean_inc(x_137);
x_151 = l_Lean_getStructureFields(x_137, x_135);
x_152 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_153 = l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1(x_1, x_2, x_135, x_137, x_151, x_152, x_3, x_118);
lean_dec(x_151);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_3, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_3, 0);
lean_inc(x_160);
lean_dec(x_3);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_158);
lean_ctor_set(x_162, 2, x_159);
lean_ctor_set(x_162, 3, x_161);
x_163 = l_Lean_Name_toString___closed__1;
x_164 = l_Lean_Name_toStringWithSep___main(x_163, x_2);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_167 = l_Lean_Meta_mkProjection___main___closed__7;
x_168 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
x_169 = l_Lean_Meta_mkProjection___main___closed__10;
x_170 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_117);
x_172 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_Meta_mkProjection___main___closed__2;
x_174 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_162);
if (lean_is_scalar(x_156)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_156;
 lean_ctor_set_tag(x_175, 1);
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_155);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = lean_ctor_get(x_153, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_177 = x_153;
} else {
 lean_dec_ref(x_153);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_154, 0);
lean_inc(x_178);
lean_dec(x_154);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_153, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_153, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_182 = x_153;
} else {
 lean_dec_ref(x_153);
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
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_150, 0);
lean_inc(x_184);
lean_dec(x_150);
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Lean_Expr_getAppNumArgsAux___main(x_117, x_185);
x_187 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_186);
x_188 = lean_mk_array(x_186, x_187);
x_189 = lean_unsigned_to_nat(1u);
x_190 = lean_nat_sub(x_186, x_189);
lean_dec(x_186);
x_191 = l___private_Lean_Expr_3__getAppArgsAux___main(x_117, x_188, x_190);
x_192 = l_Lean_mkConst(x_184, x_136);
x_193 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_191, x_191, x_185, x_192);
lean_dec(x_191);
x_194 = l_Lean_mkApp(x_193, x_1);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_118);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_134);
lean_dec(x_2);
x_196 = lean_box(0);
x_120 = x_196;
goto block_133;
}
block_133:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_120);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 0);
lean_inc(x_124);
lean_dec(x_3);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_122);
lean_ctor_set(x_126, 2, x_123);
lean_ctor_set(x_126, 3, x_125);
x_127 = l___private_Lean_Meta_AppBuilder_2__hasTypeMsg(x_1, x_117);
x_128 = l_Lean_Meta_mkProjection___main___closed__4;
x_129 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
x_130 = l_Lean_Meta_mkProjection___main___closed__2;
x_131 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_126);
if (lean_is_scalar(x_119)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_119;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_118);
return x_132;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_116, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_116, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_199 = x_116;
} else {
 lean_dec_ref(x_116);
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
}
else
{
uint8_t x_201; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_5);
if (x_201 == 0)
{
return x_5;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_5, 0);
x_203 = lean_ctor_get(x_5, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_5);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_findSomeMAux___main___at_Lean_Meta_mkProjection___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Meta_mkProjection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkProjection___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Lean_mkApp(x_2, x_4);
x_7 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(x_1, x_2, x_5);
x_8 = l_Lean_mkApp(x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_7__mkListLitAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe level, ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" is not greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_AppBuilder_8__getDecLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Meta_getLevel(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Level_dec___main(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
x_16 = l_Lean_Level_format(x_7);
x_17 = l_Lean_Options_empty;
x_18 = l_Lean_Format_pretty(x_16, x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = l_Lean_indentExpr(x_25);
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
lean_ctor_set(x_5, 0, x_29);
return x_5;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = l_Lean_Level_dec___main(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
x_39 = l_Lean_Level_format(x_30);
x_40 = l_Lean_Options_empty;
x_41 = l_Lean_Format_pretty(x_39, x_40);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_2);
x_49 = l_Lean_indentExpr(x_48);
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(16, 3, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_31);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_31);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_5);
if (x_55 == 0)
{
return x_5;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = lean_ctor_get(x_5, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_5);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkListLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkListLit");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkListLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkListLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkListLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_mkListLit___closed__2;
lean_inc(x_1);
x_6 = l___private_Lean_Meta_AppBuilder_8__getDecLevel(x_5, x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_listToExpr___rarg___closed__4;
lean_inc(x_10);
x_12 = l_Lean_mkConst(x_11, x_10);
lean_inc(x_1);
x_13 = l_Lean_mkApp(x_12, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_10);
lean_dec(x_1);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_listToExpr___rarg___closed__6;
x_15 = l_Lean_mkConst(x_14, x_10);
x_16 = l_Lean_mkApp(x_15, x_1);
x_17 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(x_13, x_16, x_2);
lean_dec(x_13);
lean_ctor_set(x_6, 0, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_listToExpr___rarg___closed__4;
lean_inc(x_21);
x_23 = l_Lean_mkConst(x_22, x_21);
lean_inc(x_1);
x_24 = l_Lean_mkApp(x_23, x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lean_listToExpr___rarg___closed__6;
x_27 = l_Lean_mkConst(x_26, x_21);
x_28 = l_Lean_mkApp(x_27, x_1);
x_29 = l___private_Lean_Meta_AppBuilder_7__mkListLitAux___main(x_24, x_28, x_2);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkArrayLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkArrayLit");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkArrayLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkArrayLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_mkArrayLit___closed__2;
lean_inc(x_3);
lean_inc(x_1);
x_6 = l___private_Lean_Meta_AppBuilder_8__getDecLevel(x_5, x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_Meta_mkListLit(x_1, x_2, x_3, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
x_15 = l_Lean_mkConst(x_14, x_13);
x_16 = l_Lean_mkApp(x_15, x_1);
x_17 = l_Lean_mkApp(x_16, x_11);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_arrayToExpr___rarg___lambda__1___closed__2;
x_23 = l_Lean_mkConst(x_22, x_21);
x_24 = l_Lean_mkApp(x_23, x_1);
x_25 = l_Lean_mkApp(x_24, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_6);
if (x_31 == 0)
{
return x_6;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sorryAx");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_boolToExpr___lambda__1___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkSorry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_boolToExpr___lambda__1___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkSorry(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getLevel(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_mkSorry___closed__2;
x_11 = l_Lean_mkConst(x_10, x_9);
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_mkSorry___closed__3;
x_13 = l_Lean_mkAppB(x_11, x_1, x_12);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_mkSorry___closed__4;
x_15 = l_Lean_mkAppB(x_11, x_1, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_mkSorry___closed__2;
x_21 = l_Lean_mkConst(x_20, x_19);
if (x_2 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Meta_mkSorry___closed__3;
x_23 = l_Lean_mkAppB(x_21, x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = l_Lean_Meta_mkSorry___closed__4;
x_26 = l_Lean_mkAppB(x_21, x_1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_mkSorry(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decide");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkDecIsTrue___closed__2;
x_2 = l_Lean_Meta_mkDecideProof___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofDecideEqTrue");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkDecideProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkDecideProof___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkDecideProof(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_mkOptionalNode___closed__2;
x_5 = lean_array_push(x_4, x_1);
x_6 = l_Lean_Meta_mkDecideProof___closed__2;
lean_inc(x_2);
x_7 = l_Lean_Meta_mkAppM(x_6, x_5, x_2, x_3);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_boolToExpr___lambda__1___closed__6;
lean_inc(x_2);
x_11 = l_Lean_Meta_mkEq(x_8, x_10, x_2, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkEqRefl(x_10, x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkExpectedTypeHint(x_15, x_12, x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_push(x_4, x_18);
x_21 = l_Lean_Meta_mkDecideProof___closed__4;
x_22 = l_Lean_Meta_mkAppM(x_21, x_20, x_2, x_19);
lean_dec(x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
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
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
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
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
return x_7;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLess");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLt___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkLt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Less");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLt___closed__2;
x_2 = l_Lean_Meta_mkLt___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkLt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Meta_mkLt___closed__4;
x_9 = l_Lean_Meta_mkAppM(x_8, x_7, x_3, x_4);
lean_dec(x_7);
return x_9;
}
}
lean_object* _init_l_Lean_Meta_mkLe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasLessEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLe___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkLe___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LessEq");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkLe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLe___closed__2;
x_2 = l_Lean_Meta_mkLe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkLe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_mkAppStx___closed__9;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_2);
x_8 = l_Lean_Meta_mkLe___closed__4;
x_9 = l_Lean_Meta_mkAppM(x_8, x_7, x_3, x_4);
lean_dec(x_7);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Structure(lean_object*);
lean_object* initialize_Lean_Util_Recognizers(lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_AppBuilder(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_mkId___closed__1 = _init_l_Lean_Meta_mkId___closed__1();
lean_mark_persistent(l_Lean_Meta_mkId___closed__1);
l_Lean_Meta_mkId___closed__2 = _init_l_Lean_Meta_mkId___closed__2();
lean_mark_persistent(l_Lean_Meta_mkId___closed__2);
l_Lean_Meta_mkEqRefl___closed__1 = _init_l_Lean_Meta_mkEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__1);
l_Lean_Meta_mkEqRefl___closed__2 = _init_l_Lean_Meta_mkEqRefl___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__2);
l_Lean_Meta_mkHEqRefl___closed__1 = _init_l_Lean_Meta_mkHEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqRefl___closed__1);
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
l_Lean_Meta_mkEqOfHEq___closed__6 = _init_l_Lean_Meta_mkEqOfHEq___closed__6();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__6);
l_Lean_Meta_mkEqOfHEq___closed__7 = _init_l_Lean_Meta_mkEqOfHEq___closed__7();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__7);
l_Lean_Meta_mkEqOfHEq___closed__8 = _init_l_Lean_Meta_mkEqOfHEq___closed__8();
lean_mark_persistent(l_Lean_Meta_mkEqOfHEq___closed__8);
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
l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1 = _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__1);
l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2 = _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__2);
l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3 = _init_l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_3__mkAppMFinal___closed__3);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__1);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__2);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__3);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__4);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__5);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__6);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__7);
l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8 = _init_l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_4__mkAppMAux___main___closed__8);
l_Lean_Meta_mkAppM___closed__1 = _init_l_Lean_Meta_mkAppM___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__1);
l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1 = _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__1);
l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2 = _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__2);
l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3 = _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__3);
l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4 = _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__4);
l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5 = _init_l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_6__mkAppOptMAux___main___closed__5);
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
l_Lean_Meta_mkEqMP___closed__1 = _init_l_Lean_Meta_mkEqMP___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqMP___closed__1);
l_Lean_Meta_mkEqMP___closed__2 = _init_l_Lean_Meta_mkEqMP___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqMP___closed__2);
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
l_Lean_Meta_mkPure___closed__1 = _init_l_Lean_Meta_mkPure___closed__1();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__1);
l_Lean_Meta_mkPure___closed__2 = _init_l_Lean_Meta_mkPure___closed__2();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__2);
l_Lean_Meta_mkPure___closed__3 = _init_l_Lean_Meta_mkPure___closed__3();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__3);
l_Lean_Meta_mkPure___closed__4 = _init_l_Lean_Meta_mkPure___closed__4();
lean_mark_persistent(l_Lean_Meta_mkPure___closed__4);
l_Lean_Meta_mkProjection___main___closed__1 = _init_l_Lean_Meta_mkProjection___main___closed__1();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__1);
l_Lean_Meta_mkProjection___main___closed__2 = _init_l_Lean_Meta_mkProjection___main___closed__2();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__2);
l_Lean_Meta_mkProjection___main___closed__3 = _init_l_Lean_Meta_mkProjection___main___closed__3();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__3);
l_Lean_Meta_mkProjection___main___closed__4 = _init_l_Lean_Meta_mkProjection___main___closed__4();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__4);
l_Lean_Meta_mkProjection___main___closed__5 = _init_l_Lean_Meta_mkProjection___main___closed__5();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__5);
l_Lean_Meta_mkProjection___main___closed__6 = _init_l_Lean_Meta_mkProjection___main___closed__6();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__6);
l_Lean_Meta_mkProjection___main___closed__7 = _init_l_Lean_Meta_mkProjection___main___closed__7();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__7);
l_Lean_Meta_mkProjection___main___closed__8 = _init_l_Lean_Meta_mkProjection___main___closed__8();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__8);
l_Lean_Meta_mkProjection___main___closed__9 = _init_l_Lean_Meta_mkProjection___main___closed__9();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__9);
l_Lean_Meta_mkProjection___main___closed__10 = _init_l_Lean_Meta_mkProjection___main___closed__10();
lean_mark_persistent(l_Lean_Meta_mkProjection___main___closed__10);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__1);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__2);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__3);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__4);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__5);
l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6 = _init_l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6();
lean_mark_persistent(l___private_Lean_Meta_AppBuilder_8__getDecLevel___closed__6);
l_Lean_Meta_mkListLit___closed__1 = _init_l_Lean_Meta_mkListLit___closed__1();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__1);
l_Lean_Meta_mkListLit___closed__2 = _init_l_Lean_Meta_mkListLit___closed__2();
lean_mark_persistent(l_Lean_Meta_mkListLit___closed__2);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
