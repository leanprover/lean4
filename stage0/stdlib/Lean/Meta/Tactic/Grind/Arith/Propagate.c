// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Propagate
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__10;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__1;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2;
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28;
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27;
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12;
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__3;
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20;
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2;
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__4;
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14;
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__6;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Lean_Expr_getAppNumArgs(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_Expr_getRevArg_x21(x_4, x_20);
x_22 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_nat_sub(x_20, x_19);
lean_dec(x_20);
x_27 = l_Lean_Expr_getRevArg_x21(x_4, x_26);
x_28 = l_Lean_Expr_isConstOf(x_27, x_22);
lean_dec_ref(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_st_ref_get(x_5);
x_32 = l_Lean_Expr_getRevArg_x21(x_4, x_19);
lean_inc_ref(x_32);
x_33 = l_Lean_Meta_Grind_Goal_getRoot(x_31, x_32, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_35 = l_Lean_Meta_getNatValue_x3f(x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_st_ref_get(x_5);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Expr_getRevArg_x21(x_4, x_40);
lean_inc_ref(x_41);
x_42 = l_Lean_Meta_Grind_Goal_getRoot(x_39, x_41, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_44 = l_Lean_Meta_getNatValue_x3f(x_43, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_apply_2(x_3, x_38, x_47);
x_49 = l_Lean_mkNatLit(x_48);
x_50 = l_Lean_Meta_Grind_shareCommon___redArg(x_49, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_51);
x_53 = lean_grind_internalize(x_51, x_40, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec_ref(x_53);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_54 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_43);
lean_inc_ref(x_41);
x_56 = lean_grind_mk_eq_proof(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_box(0);
x_59 = l_Lean_mkConst(x_2, x_58);
x_60 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2;
lean_inc(x_51);
x_61 = l_Lean_mkApp8(x_59, x_32, x_41, x_34, x_43, x_51, x_55, x_57, x_60);
x_62 = 0;
x_63 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_51, x_61, x_62, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_54);
if (x_67 == 0)
{
return x_54;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec(x_54);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_53;
}
}
else
{
uint8_t x_70; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_50);
if (x_70 == 0)
{
return x_50;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
lean_dec(x_50);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
lean_ctor_set(x_44, 0, x_73);
return x_44;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_44, 0);
lean_inc(x_74);
lean_dec(x_44);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_apply_2(x_3, x_38, x_75);
x_77 = l_Lean_mkNatLit(x_76);
x_78 = l_Lean_Meta_Grind_shareCommon___redArg(x_77, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_79);
x_81 = lean_grind_internalize(x_79, x_40, x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec_ref(x_81);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_82 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_43);
lean_inc_ref(x_41);
x_84 = lean_grind_mk_eq_proof(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_box(0);
x_87 = l_Lean_mkConst(x_2, x_86);
x_88 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2;
lean_inc(x_79);
x_89 = l_Lean_mkApp8(x_87, x_32, x_41, x_34, x_43, x_79, x_83, x_85, x_88);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_79, x_89, x_90, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_93 = x_84;
} else {
 lean_dec_ref(x_84);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_96 = x_82;
} else {
 lean_dec_ref(x_82);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
else
{
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_81;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_99 = x_78;
} else {
 lean_dec_ref(x_78);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_74);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_44);
if (x_103 == 0)
{
return x_44;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
lean_dec(x_44);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_42);
if (x_106 == 0)
{
return x_42;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_42, 0);
lean_inc(x_107);
lean_dec(x_42);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_109 = lean_box(0);
lean_ctor_set(x_35, 0, x_109);
return x_35;
}
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_35, 0);
lean_inc(x_110);
lean_dec(x_35);
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_st_ref_get(x_5);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_Expr_getRevArg_x21(x_4, x_113);
lean_inc_ref(x_114);
x_115 = l_Lean_Meta_Grind_Goal_getRoot(x_112, x_114, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_117 = l_Lean_Meta_getNatValue_x3f(x_116, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_obj_tag(x_118) == 1)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = lean_apply_2(x_3, x_111, x_120);
x_122 = l_Lean_mkNatLit(x_121);
x_123 = l_Lean_Meta_Grind_shareCommon___redArg(x_122, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_124);
x_126 = lean_grind_internalize(x_124, x_113, x_125, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_dec_ref(x_126);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_127 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_116);
lean_inc_ref(x_114);
x_129 = lean_grind_mk_eq_proof(x_114, x_116, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_box(0);
x_132 = l_Lean_mkConst(x_2, x_131);
x_133 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2;
lean_inc(x_124);
x_134 = l_Lean_mkApp8(x_132, x_32, x_114, x_34, x_116, x_124, x_128, x_130, x_133);
x_135 = 0;
x_136 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_124, x_134, x_135, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_141 = x_127;
} else {
 lean_dec_ref(x_127);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_126;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_143 = lean_ctor_get(x_123, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_144 = x_123;
} else {
 lean_dec_ref(x_123);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_118);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_146 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_119;
}
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_117, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_149 = x_117;
} else {
 lean_dec_ref(x_117);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_151 = lean_ctor_get(x_115, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_152 = x_115;
} else {
 lean_dec_ref(x_115);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_110);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_35);
if (x_156 == 0)
{
return x_35;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_35, 0);
lean_inc(x_157);
lean_dec(x_35);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_33);
if (x_159 == 0)
{
return x_33;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_33, 0);
lean_inc(x_160);
lean_dec(x_33);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and_congr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0;
x_12 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
x_13 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7;
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_congr", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0;
x_12 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
x_13 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5;
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatOr___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("xor_congr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0;
x_12 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
x_13 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5;
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatXOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftLeft_congr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0;
x_12 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
x_13 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5;
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftRight_congr", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0;
x_12 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
x_13 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5;
x_14 = l_Lean_Meta_Grind_Arith_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Name_hash___override(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(x_1, x_3, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt8", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt16", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("UInt32", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int64", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int8", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int16", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int32", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32;
x_2 = l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33;
x_3 = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__5(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(x_4, x_3);
lean_dec(x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec_ref(x_2);
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
if (x_11 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_free_object(x_18);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_21 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
if (lean_obj_tag(x_22) == 1)
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 4);
lean_inc_ref(x_28);
lean_dec(x_27);
lean_ctor_set(x_22, 0, x_28);
lean_ctor_set(x_25, 0, x_22);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 4);
lean_inc_ref(x_30);
lean_dec(x_29);
lean_ctor_set(x_22, 0, x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_22);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_22);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_22, 0);
lean_inc(x_35);
lean_dec(x_22);
x_36 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_37, 4);
lean_inc_ref(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_22);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_45 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
if (lean_obj_tag(x_47) == 1)
{
uint8_t x_48; 
lean_free_object(x_45);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_52, 3);
lean_inc_ref(x_53);
lean_dec(x_52);
lean_ctor_set(x_47, 0, x_53);
lean_ctor_set(x_50, 0, x_47);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_ctor_get(x_54, 3);
lean_inc_ref(x_55);
lean_dec(x_54);
lean_ctor_set(x_47, 0, x_55);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_47);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_free_object(x_47);
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
lean_dec(x_47);
x_61 = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_box(0);
lean_ctor_set(x_45, 0, x_70);
return x_45;
}
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_45, 0);
lean_inc(x_71);
lean_dec(x_45);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_75, 3);
lean_inc_ref(x_77);
lean_dec(x_75);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_73);
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_71);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_45);
if (x_85 == 0)
{
return x_45;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_45, 0);
lean_inc(x_86);
lean_dec(x_45);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
return x_21;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_21, 0);
lean_inc(x_89);
lean_dec(x_21);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; 
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_box(0);
lean_ctor_set(x_18, 0, x_91);
return x_18;
}
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_18, 0);
lean_inc(x_92);
lean_dec(x_18);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_93 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
x_97 = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(x_95, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_95);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_98, 4);
lean_inc_ref(x_100);
lean_dec(x_98);
if (lean_is_scalar(x_96)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_96;
}
lean_ctor_set(x_101, 0, x_100);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_96);
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_94);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_106 = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_108);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_112, 3);
lean_inc_ref(x_114);
lean_dec(x_112);
if (lean_is_scalar(x_110)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_110;
}
lean_ctor_set(x_115, 0, x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_110);
x_117 = lean_ctor_get(x_111, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_107);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_108;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_106, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_123 = x_106;
} else {
 lean_dec_ref(x_106);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_125 = lean_ctor_get(x_93, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_126 = x_93;
} else {
 lean_dec_ref(x_93);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec_ref(x_92);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_130 = !lean_is_exclusive(x_18);
if (x_130 == 0)
{
return x_18;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_18, 0);
lean_inc(x_131);
lean_dec(x_18);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_17;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_17;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_14;
}
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_133; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_133 = !lean_is_exclusive(x_12);
if (x_133 == 0)
{
return x_12;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_12, 0);
lean_inc(x_134);
lean_dec(x_12);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec_ref(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_13);
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_13);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2;
x_19 = l_Lean_Expr_isConstOf(x_17, x_18);
lean_dec_ref(x_17);
if (x_19 == 0)
{
lean_dec_ref(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_20);
lean_dec_ref(x_13);
x_21 = l_Lean_Meta_getNatValue_x3f(x_20, x_2, x_3, x_4, x_5);
lean_dec_ref(x_20);
return x_21;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateMul___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Semiring", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("one_mul_congr", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateMul___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero_mul_congr", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateMul___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_one_congr", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateMul___closed__8;
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul_zero_congr", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_propagateMul___closed__10;
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__3;
x_3 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_1);
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc_ref(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_30);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_309; uint8_t x_310; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_15);
x_36 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_17);
x_309 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_309);
lean_dec_ref(x_23);
x_310 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_30, x_309);
lean_dec_ref(x_309);
if (x_310 == 0)
{
lean_dec_ref(x_21);
x_37 = x_310;
goto block_308;
}
else
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_311);
lean_dec_ref(x_21);
x_312 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_30, x_311);
lean_dec_ref(x_311);
x_37 = x_312;
goto block_308;
}
block_308:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
if (lean_obj_tag(x_40) == 1)
{
uint8_t x_41; 
lean_dec(x_33);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_dec(x_43);
x_44 = lean_st_ref_get(x_2);
lean_inc_ref(x_36);
x_45 = l_Lean_Meta_Grind_Goal_getRoot(x_44, x_36, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_st_ref_get(x_2);
lean_inc_ref(x_35);
x_48 = l_Lean_Meta_Grind_Goal_getRoot(x_47, x_35, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_46);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_46, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_dec_eq(x_53, x_56);
lean_dec(x_53);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_50, 0, x_58);
return x_50;
}
else
{
lean_object* x_59; 
lean_free_object(x_50);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_36);
x_59 = lean_grind_mk_eq_proof(x_36, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
x_62 = lean_box(0);
lean_ctor_set(x_40, 1, x_62);
x_63 = l_Lean_mkConst(x_61, x_40);
lean_inc_ref(x_35);
x_64 = l_Lean_mkApp5(x_63, x_30, x_34, x_36, x_35, x_60);
x_65 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_35, x_64, x_55, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_65;
}
else
{
uint8_t x_66; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_53);
lean_free_object(x_50);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_46);
lean_inc_ref(x_36);
x_69 = lean_grind_mk_eq_proof(x_36, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
x_72 = lean_box(0);
lean_ctor_set(x_40, 1, x_72);
x_73 = l_Lean_mkConst(x_71, x_40);
x_74 = l_Lean_mkApp5(x_73, x_30, x_34, x_36, x_35, x_70);
x_75 = 0;
x_76 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_46, x_74, x_75, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_76;
}
else
{
uint8_t x_77; 
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_77 = !lean_is_exclusive(x_69);
if (x_77 == 0)
{
return x_69;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_dec(x_69);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; 
lean_free_object(x_50);
lean_dec(x_52);
lean_dec(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_49);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_dec_eq(x_83, x_86);
lean_dec(x_83);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = lean_box(0);
lean_ctor_set(x_80, 0, x_88);
return x_80;
}
else
{
lean_object* x_89; 
lean_free_object(x_80);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_35);
x_89 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
x_92 = lean_box(0);
lean_ctor_set(x_40, 1, x_92);
x_93 = l_Lean_mkConst(x_91, x_40);
lean_inc_ref(x_36);
x_94 = l_Lean_mkApp5(x_93, x_30, x_34, x_36, x_35, x_90);
x_95 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_36, x_94, x_85, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_95;
}
else
{
uint8_t x_96; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_89);
if (x_96 == 0)
{
return x_89;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_89, 0);
lean_inc(x_97);
lean_dec(x_89);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_83);
lean_free_object(x_80);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_49);
lean_inc_ref(x_35);
x_99 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec_ref(x_99);
x_101 = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
x_102 = lean_box(0);
lean_ctor_set(x_40, 1, x_102);
x_103 = l_Lean_mkConst(x_101, x_40);
x_104 = l_Lean_mkApp5(x_103, x_30, x_34, x_36, x_35, x_100);
x_105 = 0;
x_106 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_49, x_104, x_105, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_106;
}
else
{
uint8_t x_107; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_99);
if (x_107 == 0)
{
return x_99;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_99, 0);
lean_inc(x_108);
lean_dec(x_99);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_110; 
lean_dec(x_82);
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_110 = lean_box(0);
lean_ctor_set(x_80, 0, x_110);
return x_80;
}
}
else
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_80, 0);
lean_inc(x_111);
lean_dec(x_80);
if (lean_obj_tag(x_111) == 1)
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_nat_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_dec_eq(x_112, x_115);
lean_dec(x_112);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
else
{
lean_object* x_119; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_35);
x_119 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
x_122 = lean_box(0);
lean_ctor_set(x_40, 1, x_122);
x_123 = l_Lean_mkConst(x_121, x_40);
lean_inc_ref(x_36);
x_124 = l_Lean_mkApp5(x_123, x_30, x_34, x_36, x_35, x_120);
x_125 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_36, x_124, x_114, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_127 = x_119;
} else {
 lean_dec_ref(x_119);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_112);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_49);
lean_inc_ref(x_35);
x_129 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
x_132 = lean_box(0);
lean_ctor_set(x_40, 1, x_132);
x_133 = l_Lean_mkConst(x_131, x_40);
x_134 = l_Lean_mkApp5(x_133, x_30, x_34, x_36, x_35, x_130);
x_135 = 0;
x_136 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_49, x_134, x_135, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_111);
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_80);
if (x_142 == 0)
{
return x_80;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_80, 0);
lean_inc(x_143);
lean_dec(x_80);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_50, 0);
lean_inc(x_145);
lean_dec(x_50);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_49);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_nat_dec_eq(x_146, x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_dec_eq(x_146, x_149);
lean_dec(x_146);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
return x_152;
}
else
{
lean_object* x_153; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_36);
x_153 = lean_grind_mk_eq_proof(x_36, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
x_156 = lean_box(0);
lean_ctor_set(x_40, 1, x_156);
x_157 = l_Lean_mkConst(x_155, x_40);
lean_inc_ref(x_35);
x_158 = l_Lean_mkApp5(x_157, x_30, x_34, x_36, x_35, x_154);
x_159 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_35, x_158, x_148, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_160 = lean_ctor_get(x_153, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_161 = x_153;
} else {
 lean_dec_ref(x_153);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_146);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_46);
lean_inc_ref(x_36);
x_163 = lean_grind_mk_eq_proof(x_36, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
x_166 = lean_box(0);
lean_ctor_set(x_40, 1, x_166);
x_167 = l_Lean_mkConst(x_165, x_40);
x_168 = l_Lean_mkApp5(x_167, x_30, x_34, x_36, x_35, x_164);
x_169 = 0;
x_170 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_46, x_168, x_169, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_171 = lean_ctor_get(x_163, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
}
}
else
{
lean_object* x_174; 
lean_dec(x_145);
lean_dec(x_46);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_49);
x_174 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_49, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_obj_tag(x_175) == 1)
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_nat_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_dec_eq(x_177, x_180);
lean_dec(x_177);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_182 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
else
{
lean_object* x_184; 
lean_dec(x_176);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_35);
x_184 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
x_187 = lean_box(0);
lean_ctor_set(x_40, 1, x_187);
x_188 = l_Lean_mkConst(x_186, x_40);
lean_inc_ref(x_36);
x_189 = l_Lean_mkApp5(x_188, x_30, x_34, x_36, x_35, x_185);
x_190 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_36, x_189, x_179, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_184, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_192 = x_184;
} else {
 lean_dec_ref(x_184);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; 
lean_dec(x_177);
lean_dec(x_176);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_49);
lean_inc_ref(x_35);
x_194 = lean_grind_mk_eq_proof(x_35, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
x_197 = lean_box(0);
lean_ctor_set(x_40, 1, x_197);
x_198 = l_Lean_mkConst(x_196, x_40);
x_199 = l_Lean_mkApp5(x_198, x_30, x_34, x_36, x_35, x_195);
x_200 = 0;
x_201 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_49, x_199, x_200, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_203 = x_194;
} else {
 lean_dec_ref(x_194);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_175);
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_205 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_176;
}
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_49);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_207 = lean_ctor_get(x_174, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_208 = x_174;
} else {
 lean_dec_ref(x_174);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_49);
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_210 = !lean_is_exclusive(x_50);
if (x_210 == 0)
{
return x_50;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_50, 0);
lean_inc(x_211);
lean_dec(x_50);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_48);
if (x_213 == 0)
{
return x_48;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_48, 0);
lean_inc(x_214);
lean_dec(x_48);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_216 = !lean_is_exclusive(x_45);
if (x_216 == 0)
{
return x_45;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_45, 0);
lean_inc(x_217);
lean_dec(x_45);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_40, 0);
lean_inc(x_219);
lean_dec(x_40);
x_220 = lean_st_ref_get(x_2);
lean_inc_ref(x_36);
x_221 = l_Lean_Meta_Grind_Goal_getRoot(x_220, x_36, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = lean_st_ref_get(x_2);
lean_inc_ref(x_35);
x_224 = l_Lean_Meta_Grind_Goal_getRoot(x_223, x_35, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_222);
x_226 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_222, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
if (lean_obj_tag(x_227) == 1)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_225);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
lean_dec_ref(x_227);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_eq(x_229, x_230);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_dec_eq(x_229, x_232);
lean_dec(x_229);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_234 = lean_box(0);
if (lean_is_scalar(x_228)) {
 x_235 = lean_alloc_ctor(0, 1, 0);
} else {
 x_235 = x_228;
}
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
else
{
lean_object* x_236; 
lean_dec(x_228);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_36);
x_236 = lean_grind_mk_eq_proof(x_36, x_222, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = l_Lean_Meta_Grind_Arith_propagateMul___closed__5;
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_219);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_mkConst(x_238, x_240);
lean_inc_ref(x_35);
x_242 = l_Lean_mkApp5(x_241, x_30, x_34, x_36, x_35, x_237);
x_243 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_35, x_242, x_231, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_244 = lean_ctor_get(x_236, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_245 = x_236;
} else {
 lean_dec_ref(x_236);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_244);
return x_246;
}
}
}
else
{
lean_object* x_247; 
lean_dec(x_229);
lean_dec(x_228);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_222);
lean_inc_ref(x_36);
x_247 = lean_grind_mk_eq_proof(x_36, x_222, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
x_249 = l_Lean_Meta_Grind_Arith_propagateMul___closed__7;
x_250 = lean_box(0);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_219);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_mkConst(x_249, x_251);
x_253 = l_Lean_mkApp5(x_252, x_30, x_34, x_36, x_35, x_248);
x_254 = 0;
x_255 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_222, x_253, x_254, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_256 = lean_ctor_get(x_247, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 x_257 = x_247;
} else {
 lean_dec_ref(x_247);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
}
else
{
lean_object* x_259; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_222);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_225);
x_259 = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(x_225, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_obj_tag(x_260) == 1)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
lean_dec_ref(x_260);
x_263 = lean_unsigned_to_nat(0u);
x_264 = lean_nat_dec_eq(x_262, x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_dec_eq(x_262, x_265);
lean_dec(x_262);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_225);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_267 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_261;
}
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
else
{
lean_object* x_269; 
lean_dec(x_261);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_35);
x_269 = lean_grind_mk_eq_proof(x_35, x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
lean_dec_ref(x_269);
x_271 = l_Lean_Meta_Grind_Arith_propagateMul___closed__9;
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_219);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Lean_mkConst(x_271, x_273);
lean_inc_ref(x_36);
x_275 = l_Lean_mkApp5(x_274, x_30, x_34, x_36, x_35, x_270);
x_276 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_36, x_275, x_264, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_277 = lean_ctor_get(x_269, 0);
lean_inc(x_277);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 x_278 = x_269;
} else {
 lean_dec_ref(x_269);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_277);
return x_279;
}
}
}
else
{
lean_object* x_280; 
lean_dec(x_262);
lean_dec(x_261);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc(x_225);
lean_inc_ref(x_35);
x_280 = lean_grind_mk_eq_proof(x_35, x_225, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = l_Lean_Meta_Grind_Arith_propagateMul___closed__11;
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_219);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_mkConst(x_282, x_284);
x_286 = l_Lean_mkApp5(x_285, x_30, x_34, x_36, x_35, x_281);
x_287 = 0;
x_288 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_225, x_286, x_287, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_225);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_289 = lean_ctor_get(x_280, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_290 = x_280;
} else {
 lean_dec_ref(x_280);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_289);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_260);
lean_dec(x_225);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_292 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_293 = lean_alloc_ctor(0, 1, 0);
} else {
 x_293 = x_261;
}
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_225);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_294 = lean_ctor_get(x_259, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_295 = x_259;
} else {
 lean_dec_ref(x_259);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 1, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_294);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_225);
lean_dec(x_222);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_297 = lean_ctor_get(x_226, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_298 = x_226;
} else {
 lean_dec_ref(x_226);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_222);
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_224, 0);
lean_inc(x_300);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_301 = x_224;
} else {
 lean_dec_ref(x_224);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 1, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_300);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_219);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_303 = lean_ctor_get(x_221, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 x_304 = x_221;
} else {
 lean_dec_ref(x_221);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_303);
return x_305;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_40);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_306 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_307 = lean_alloc_ctor(0, 1, 0);
} else {
 x_307 = x_33;
}
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_32);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_313 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_314 = lean_alloc_ctor(0, 1, 0);
} else {
 x_314 = x_33;
}
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
}
else
{
uint8_t x_315; 
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_315 = !lean_is_exclusive(x_31);
if (x_315 == 0)
{
return x_31;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_31, 0);
lean_inc(x_316);
lean_dec(x_31);
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_316);
return x_317;
}
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateMul___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6);
l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7 = _init_l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3);
l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4);
l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3);
l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4);
l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3);
l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4);
l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0);
l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1);
l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2);
l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3);
l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4);
l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2);
l_Lean_Meta_Grind_Arith_propagateMul___closed__0 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__0);
l_Lean_Meta_Grind_Arith_propagateMul___closed__1 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__1);
l_Lean_Meta_Grind_Arith_propagateMul___closed__2 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__2);
l_Lean_Meta_Grind_Arith_propagateMul___closed__3 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__3);
l_Lean_Meta_Grind_Arith_propagateMul___closed__4 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__4);
l_Lean_Meta_Grind_Arith_propagateMul___closed__5 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__5);
l_Lean_Meta_Grind_Arith_propagateMul___closed__6 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__6);
l_Lean_Meta_Grind_Arith_propagateMul___closed__7 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__7);
l_Lean_Meta_Grind_Arith_propagateMul___closed__8 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__8);
l_Lean_Meta_Grind_Arith_propagateMul___closed__9 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__9);
l_Lean_Meta_Grind_Arith_propagateMul___closed__10 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__10);
l_Lean_Meta_Grind_Arith_propagateMul___closed__11 = _init_l_Lean_Meta_Grind_Arith_propagateMul___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateMul___closed__11);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
