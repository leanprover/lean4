// Lean compiler output
// Module: Lean.Meta.Tactic.ElimInfo
// Imports: Init Lean.Meta.Basic Lean.Meta.Check
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
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getElimInfo___lambda__4___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_getElimInfo___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimInfo_altsInfo___default;
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2;
uint8_t l_USize_decLt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimInfo;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__4(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getElimInfo___lambda__4___closed__1;
static lean_object* l_Lean_Meta_getElimInfo___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReprElimInfo___closed__1;
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9;
static lean_object* l_Lean_Meta_addImplicitTargets_collect___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7(lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8;
static lean_object* l_Lean_Meta_addImplicitTargets_collect___closed__4;
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1;
static lean_object* l_Lean_Meta_addImplicitTargets_collect___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15;
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2;
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getElimInfo___lambda__1___closed__2;
static lean_object* l_Lean_Meta_getElimInfo___lambda__2___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addImplicitTargets_collect___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13;
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
static lean_object* l_Lean_Meta_getElimInfo___lambda__4___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_instReprElimAltInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getElimInfo___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__1(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6;
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_getElimInfo___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ElimInfo_targetsPos___default___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15;
static lean_object* l_Lean_Meta_instReprElimAltInfo___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14;
static lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3;
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__2(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimInfo_targetsPos___default;
static lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5;
uint8_t l_Lean_Expr_isSort(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1;
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" := ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3;
x_2 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("numFields");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{ ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" }");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Nat_repr(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13;
x_25 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = 0;
x_27 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimAltInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprElimAltInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimInfo_targetsPos___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ElimInfo_targetsPos___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ElimInfo_targetsPos___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ElimInfo_altsInfo___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_ElimInfo_targetsPos___default___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22_(x_8, x_9);
lean_inc(x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__3(x_4, x_2);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__1(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_repr___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__1(x_7);
lean_inc(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__4(x_4, x_2);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motivePos");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("targetsPos");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("altsInfo");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#[");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("#[]");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = l_Nat_repr(x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_8);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
x_22 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4;
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = lean_array_get_size(x_25);
x_27 = lean_nat_dec_eq(x_26, x_4);
lean_dec(x_26);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_eq(x_29, x_4);
lean_dec(x_29);
if (x_27 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_69 = lean_array_to_list(lean_box(0), x_25);
x_70 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7;
x_71 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__4(x_69, x_70);
x_72 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11;
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13;
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10;
x_77 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = 1;
x_79 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_31 = x_79;
goto block_68;
}
else
{
lean_object* x_80; 
lean_dec(x_25);
x_80 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15;
x_31 = x_80;
goto block_68;
}
block_68:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
x_35 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6;
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_14);
if (x_30 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_38 = lean_array_to_list(lean_box(0), x_28);
x_39 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7;
x_40 = l_Std_Format_joinSep___at___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____spec__3(x_38, x_39);
x_41 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13;
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10;
x_46 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = 1;
x_48 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14;
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13;
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = 0;
x_57 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_28);
x_58 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15;
x_59 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_59, 0, x_37);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16;
x_63 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13;
x_65 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = 0;
x_67 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReprElimInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReprElimInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_expr_eqv(x_7, x_2);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected eliminator type");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_4 < x_3;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = x_5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
x_17 = x_14;
x_18 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_2, x_17, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_16);
x_19 = l_Lean_indentExpr(x_1);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Meta_getLevelMVarDepth___spec__1(x_23, x_6, x_7, x_8, x_9, x_10);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = 1;
x_31 = x_4 + x_30;
x_32 = x_29;
x_33 = lean_array_uset(x_16, x_4, x_32);
x_4 = x_31;
x_5 = x_33;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_expr_eqv(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_getElimInfo___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_le(x_13, x_6);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_array_get(x_26, x_1, x_6);
x_28 = lean_expr_eqv(x_27, x_2);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__4(x_3, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Expr_fvarId_x21(x_27);
lean_dec(x_27);
lean_inc(x_8);
x_31 = l_Lean_Meta_getLocalDecl(x_30, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_LocalDecl_binderInfo(x_32);
x_35 = l_Lean_BinderInfo_isExplicit(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_7);
x_19 = x_36;
x_20 = x_33;
goto block_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_Lean_LocalDecl_type(x_32);
x_38 = l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_37, x_38, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_LocalDecl_userName(x_32);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_array_push(x_7, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_19 = x_45;
x_20 = x_41;
goto block_25;
}
else
{
uint8_t x_46; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_27);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_7);
x_19 = x_54;
x_20 = x_12;
goto block_25;
}
}
else
{
lean_object* x_55; 
lean_dec(x_27);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_7);
x_19 = x_55;
x_20 = x_12;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_4, 2);
x_23 = lean_nat_add(x_6, x_22);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_23;
x_7 = x_21;
x_12 = x_20;
goto _start;
}
}
else
{
lean_object* x_56; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_7);
lean_ctor_set(x_56, 1, x_12);
return x_56;
}
}
else
{
lean_object* x_57; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_7);
lean_ctor_set(x_57, 1, x_12);
return x_57;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isFVar(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive result type must be a sort");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getElimInfo___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_isSort(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_indentExpr(x_2);
x_11 = l_Lean_Meta_getElimInfo___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected number of arguments at motive type");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getElimInfo___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_3);
lean_dec(x_3);
x_11 = lean_array_get_size(x_2);
lean_dec(x_2);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
x_13 = l_Lean_indentExpr(x_1);
x_14 = l_Lean_Meta_getElimInfo___lambda__2___closed__2;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_17, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Meta_getElimInfo___lambda__1(x_4, x_1, x_23, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_2);
lean_inc(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_getElimInfo___lambda__2), 9, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_13, x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_3, x_1, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = l_Lean_indentExpr(x_4);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2(x_24, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_array_get_size(x_2);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
lean_inc(x_2);
x_29 = x_2;
x_30 = lean_box_usize(x_28);
x_31 = l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1;
lean_inc(x_3);
x_32 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___boxed), 10, 5);
lean_closure_set(x_32, 0, x_4);
lean_closure_set(x_32, 1, x_3);
lean_closure_set(x_32, 2, x_30);
lean_closure_set(x_32, 3, x_31);
lean_closure_set(x_32, 4, x_29);
x_33 = x_32;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_34 = lean_apply_5(x_33, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_array_get_size(x_3);
x_38 = lean_unsigned_to_nat(1u);
lean_inc(x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Lean_Meta_ElimInfo_targetsPos___default___closed__1;
x_41 = l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6(x_3, x_1, x_2, x_39, x_37, x_18, x_40, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_1);
lean_dec(x_3);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_26);
lean_ctor_set(x_44, 2, x_35);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_41, 0);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_41);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_26);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_26);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
return x_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_41);
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
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
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
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_16);
if (x_57 == 0)
{
return x_16;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_16, 0);
x_59 = lean_ctor_get(x_16, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
return x_12;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_12, 0);
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_12);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected eliminator resulting type");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getElimInfo___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getElimInfo___lambda__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_30; uint8_t x_46; 
x_10 = l_Lean_Expr_getAppFn(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_4, x_11);
x_13 = l_Lean_Meta_getElimInfo___lambda__4___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
lean_inc(x_4);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_14, x_16);
x_46 = l_Lean_Expr_isFVar(x_10);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_18 = x_47;
goto block_29;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_get_size(x_17);
x_49 = lean_nat_dec_lt(x_11, x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
x_50 = lean_box(0);
x_30 = x_50;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_48, x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
x_52 = lean_box(0);
x_30 = x_52;
goto block_45;
}
else
{
size_t x_53; size_t x_54; uint8_t x_55; 
x_53 = 0;
x_54 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_55 = l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7(x_17, x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_30 = x_56;
goto block_45;
}
else
{
lean_object* x_57; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_18 = x_57;
goto block_29;
}
}
}
}
block_29:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_18);
x_19 = l_Lean_indentExpr(x_4);
x_20 = l_Lean_Meta_getElimInfo___lambda__4___closed__3;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_23, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
block_45:
{
lean_object* x_31; uint8_t x_32; 
lean_dec(x_30);
x_31 = lean_array_get_size(x_17);
x_32 = lean_nat_dec_lt(x_11, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = l_Lean_indentExpr(x_4);
x_34 = l_Lean_Meta_getElimInfo___lambda__4___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_37, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_getElimInfo___lambda__3(x_10, x_17, x_3, x_1, x_2, x_43, x_5, x_6, x_7, x_8, x_9);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_ConstantInfo_type(x_8);
lean_dec(x_8);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getElimInfo___lambda__4), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_getElimInfo___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__5(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_getElimInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_getElimInfo___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Meta_getElimInfo___spec__7(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getElimInfo___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getElimInfo___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_nat_dec_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_14 = lean_expr_instantiate1(x_1, x_2);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_17 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_18 = lean_array_push(x_5, x_2);
x_19 = l_Lean_Meta_addImplicitTargets_collect(x_6, x_7, x_14, x_16, x_17, x_18, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("target");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_array_get(x_14, x_1, x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_17);
lean_inc(x_3);
x_19 = l_Lean_Meta_isExprDefEq(x_3, x_17, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_17, x_3, x_9, x_10, x_11, x_12, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_indentExpr(x_15);
x_27 = l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_33, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_17);
lean_dec(x_3);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_dec(x_19);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_addImplicitTargets_collect___lambda__1(x_4, x_15, x_5, x_2, x_6, x_7, x_1, x_40, x_9, x_10, x_11, x_12, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("insufficient number of targets for '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addImplicitTargets_collect___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets_collect___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_addImplicitTargets_collect___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_whnfD(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(x_19, x_4);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = 0;
x_23 = lean_box(0);
lean_inc(x_7);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_23, x_7, x_8, x_9, x_10, x_14);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_expr_instantiate1(x_16, x_25);
lean_dec(x_25);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_4, x_28);
lean_dec(x_4);
x_3 = x_27;
x_4 = x_29;
x_11 = x_26;
goto _start;
}
else
{
uint8_t x_31; uint8_t x_32; 
x_31 = (uint8_t)((x_17 << 24) >> 61);
x_32 = l_Lean_BinderInfo_isExplicit(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_15);
x_34 = 0;
x_35 = lean_box(0);
lean_inc(x_7);
x_36 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_33, x_34, x_35, x_7, x_8, x_9, x_10, x_14);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_expr_instantiate1(x_16, x_37);
lean_dec(x_16);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_4, x_40);
lean_dec(x_4);
x_42 = lean_array_push(x_6, x_37);
x_3 = x_39;
x_4 = x_41;
x_6 = x_42;
x_11 = x_38;
goto _start;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_array_get_size(x_2);
x_45 = lean_nat_dec_lt(x_5, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_18);
x_47 = l_Lean_Meta_addImplicitTargets_collect___closed__2;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Meta_addImplicitTargets_collect___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_50, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_18);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_addImplicitTargets_collect___lambda__2(x_2, x_5, x_15, x_16, x_4, x_6, x_1, x_56, x_7, x_8, x_9, x_10, x_14);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_12, 0);
lean_dec(x_59);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_addImplicitTargets_collect___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Meta_addImplicitTargets_collect___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_instantiateMVars(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_17;
x_22 = lean_array_uset(x_14, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to infer implicit target, it contains unresolved metavariables");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_12);
x_13 = l_Lean_Meta_hasAssignableMVar(x_12, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = 1;
x_18 = x_3 + x_17;
x_19 = lean_box(0);
x_3 = x_18;
x_4 = x_19;
x_9 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_indentExpr(x_12);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at_Lean_Meta_withIncRecDepth___spec__1(x_26, x_5, x_6, x_7, x_8, x_21);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
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
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3___rarg), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Meta_ElimInfo_targetsPos___default___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Meta_addImplicitTargets_collect(x_2, x_3, x_13, x_15, x_15, x_16, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = x_18;
x_24 = lean_box_usize(x_21);
x_25 = l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1;
x_26 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1___boxed), 8, 3);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_23);
x_27 = x_26;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = lean_apply_5(x_27, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_get_size(x_29);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2(x_29, x_32, x_22, x_33, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_29);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_29);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_28);
if (x_43 == 0)
{
return x_28;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImplicitTargets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_addImplicitTargets___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_addImplicitTargets___spec__3___rarg(x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_addImplicitTargets___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
lean_object* initialize_Lean_Meta_Check(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_ElimInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__1);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__2);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__3);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__4);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__5);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__6);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__7);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__8);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__9);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__10);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__11);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__12);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__13);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__14);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__15);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimAltInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_22____closed__16);
l_Lean_Meta_instReprElimAltInfo___closed__1 = _init_l_Lean_Meta_instReprElimAltInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprElimAltInfo___closed__1);
l_Lean_Meta_instReprElimAltInfo = _init_l_Lean_Meta_instReprElimAltInfo();
lean_mark_persistent(l_Lean_Meta_instReprElimAltInfo);
l_Lean_Meta_ElimInfo_targetsPos___default___closed__1 = _init_l_Lean_Meta_ElimInfo_targetsPos___default___closed__1();
lean_mark_persistent(l_Lean_Meta_ElimInfo_targetsPos___default___closed__1);
l_Lean_Meta_ElimInfo_targetsPos___default = _init_l_Lean_Meta_ElimInfo_targetsPos___default();
lean_mark_persistent(l_Lean_Meta_ElimInfo_targetsPos___default);
l_Lean_Meta_ElimInfo_altsInfo___default = _init_l_Lean_Meta_ElimInfo_altsInfo___default();
lean_mark_persistent(l_Lean_Meta_ElimInfo_altsInfo___default);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__1);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__2);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__3);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__4);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__5);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__6);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__7);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__8);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__9);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__10);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__11);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__12);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__13);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__14);
l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15 = _init_l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_ElimInfo_0__Lean_Meta_reprElimInfo____x40_Lean_Meta_Tactic_ElimInfo___hyg_95____closed__15);
l_Lean_Meta_instReprElimInfo___closed__1 = _init_l_Lean_Meta_instReprElimInfo___closed__1();
lean_mark_persistent(l_Lean_Meta_instReprElimInfo___closed__1);
l_Lean_Meta_instReprElimInfo = _init_l_Lean_Meta_instReprElimInfo();
lean_mark_persistent(l_Lean_Meta_instReprElimInfo);
l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_getElimInfo___spec__3___closed__4);
l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_getElimInfo___spec__6___closed__1);
l_Lean_Meta_getElimInfo___lambda__1___closed__1 = _init_l_Lean_Meta_getElimInfo___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__1___closed__1);
l_Lean_Meta_getElimInfo___lambda__1___closed__2 = _init_l_Lean_Meta_getElimInfo___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__1___closed__2);
l_Lean_Meta_getElimInfo___lambda__2___closed__1 = _init_l_Lean_Meta_getElimInfo___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__2___closed__1);
l_Lean_Meta_getElimInfo___lambda__2___closed__2 = _init_l_Lean_Meta_getElimInfo___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__2___closed__2);
l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1 = _init_l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__3___boxed__const__1);
l_Lean_Meta_getElimInfo___lambda__4___closed__1 = _init_l_Lean_Meta_getElimInfo___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__4___closed__1);
l_Lean_Meta_getElimInfo___lambda__4___closed__2 = _init_l_Lean_Meta_getElimInfo___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__4___closed__2);
l_Lean_Meta_getElimInfo___lambda__4___closed__3 = _init_l_Lean_Meta_getElimInfo___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_getElimInfo___lambda__4___closed__3);
l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1 = _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__1);
l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2 = _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__2);
l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3 = _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__3);
l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4 = _init_l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___lambda__2___closed__4);
l_Lean_Meta_addImplicitTargets_collect___closed__1 = _init_l_Lean_Meta_addImplicitTargets_collect___closed__1();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___closed__1);
l_Lean_Meta_addImplicitTargets_collect___closed__2 = _init_l_Lean_Meta_addImplicitTargets_collect___closed__2();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___closed__2);
l_Lean_Meta_addImplicitTargets_collect___closed__3 = _init_l_Lean_Meta_addImplicitTargets_collect___closed__3();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___closed__3);
l_Lean_Meta_addImplicitTargets_collect___closed__4 = _init_l_Lean_Meta_addImplicitTargets_collect___closed__4();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets_collect___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_addImplicitTargets___spec__2___closed__2);
l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1 = _init_l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_addImplicitTargets___lambda__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
