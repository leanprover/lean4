// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagateInj
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Propagator import Init.Grind.Injective import Lean.Meta.Tactic.Grind.Proof import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Injective
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0;
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_preprocessLight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object**);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8;
static lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4;
lean_object* l_Lean_Expr_eta(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__5;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10;
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__0;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9;
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__1;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__3;
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1____x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(lean_object*);
uint64_t l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_mkInjEq___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(x_1, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_4, 2);
lean_inc(x_24);
lean_inc_ref(x_23);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_3, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_4, 2);
lean_inc(x_36);
lean_inc_ref(x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(3, 2, 0);
} else {
 x_38 = x_33;
 lean_ctor_set_tag(x_38, 3);
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_st_ref_take(x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_15);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 4);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; double x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
x_24 = 0;
x_25 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_24);
x_27 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_8);
x_29 = l_Lean_PersistentArray_push___redArg(x_22, x_13);
lean_ctor_set(x_15, 0, x_29);
x_30 = lean_st_ref_set(x_6, x_14, x_17);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_box(0);
lean_ctor_set(x_9, 1, x_31);
lean_ctor_set(x_9, 0, x_32);
return x_9;
}
else
{
uint64_t x_33; lean_object* x_34; double x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
x_36 = 0;
x_37 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
x_38 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_float(x_38, sizeof(void*)*2, x_35);
lean_ctor_set_float(x_38, sizeof(void*)*2 + 8, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 16, x_36);
x_39 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
x_40 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set(x_40, 2, x_39);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_40);
lean_ctor_set(x_13, 0, x_8);
x_41 = l_Lean_PersistentArray_push___redArg(x_34, x_13);
x_42 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint64(x_42, sizeof(void*)*1, x_33);
lean_ctor_set(x_14, 4, x_42);
x_43 = lean_st_ref_set(x_6, x_14, x_17);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_box(0);
lean_ctor_set(x_9, 1, x_44);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; double x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
x_48 = lean_ctor_get(x_14, 2);
x_49 = lean_ctor_get(x_14, 3);
x_50 = lean_ctor_get(x_14, 5);
x_51 = lean_ctor_get(x_14, 6);
x_52 = lean_ctor_get(x_14, 7);
x_53 = lean_ctor_get(x_14, 8);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_54 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_55 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_56 = x_15;
} else {
 lean_dec_ref(x_15);
 x_56 = lean_box(0);
}
x_57 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
x_58 = 0;
x_59 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
x_60 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_float(x_60, sizeof(void*)*2, x_57);
lean_ctor_set_float(x_60, sizeof(void*)*2 + 8, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*2 + 16, x_58);
x_61 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
x_62 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set(x_62, 2, x_61);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_62);
lean_ctor_set(x_13, 0, x_8);
x_63 = l_Lean_PersistentArray_push___redArg(x_55, x_13);
if (lean_is_scalar(x_56)) {
 x_64 = lean_alloc_ctor(0, 1, 8);
} else {
 x_64 = x_56;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint64(x_64, sizeof(void*)*1, x_54);
x_65 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_47);
lean_ctor_set(x_65, 2, x_48);
lean_ctor_set(x_65, 3, x_49);
lean_ctor_set(x_65, 4, x_64);
lean_ctor_set(x_65, 5, x_50);
lean_ctor_set(x_65, 6, x_51);
lean_ctor_set(x_65, 7, x_52);
lean_ctor_set(x_65, 8, x_53);
x_66 = lean_st_ref_set(x_6, x_65, x_17);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_box(0);
lean_ctor_set(x_9, 1, x_67);
lean_ctor_set(x_9, 0, x_68);
return x_9;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; double x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_69 = lean_ctor_get(x_13, 1);
lean_inc(x_69);
lean_dec(x_13);
x_70 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_14, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_14, 2);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_14, 5);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_14, 6);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_14, 7);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_14, 8);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 lean_ctor_release(x_14, 6);
 lean_ctor_release(x_14, 7);
 lean_ctor_release(x_14, 8);
 x_78 = x_14;
} else {
 lean_dec_ref(x_14);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get_uint64(x_15, sizeof(void*)*1);
x_80 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_81 = x_15;
} else {
 lean_dec_ref(x_15);
 x_81 = lean_box(0);
}
x_82 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
x_83 = 0;
x_84 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
x_85 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_float(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_float(x_85, sizeof(void*)*2 + 8, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 16, x_83);
x_86 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
x_87 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_11);
lean_ctor_set(x_87, 2, x_86);
lean_inc(x_8);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_8);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_PersistentArray_push___redArg(x_80, x_88);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 1, 8);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint64(x_90, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 9, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_70);
lean_ctor_set(x_91, 1, x_71);
lean_ctor_set(x_91, 2, x_72);
lean_ctor_set(x_91, 3, x_73);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_74);
lean_ctor_set(x_91, 6, x_75);
lean_ctor_set(x_91, 7, x_76);
lean_ctor_set(x_91, 8, x_77);
x_92 = lean_st_ref_set(x_6, x_91, x_69);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_box(0);
lean_ctor_set(x_9, 1, x_93);
lean_ctor_set(x_9, 0, x_94);
return x_9;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; lean_object* x_112; lean_object* x_113; double x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_97 = lean_st_ref_take(x_6, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 4);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 2);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_98, 3);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_98, 5);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_98, 6);
lean_inc_ref(x_107);
x_108 = lean_ctor_get(x_98, 7);
lean_inc_ref(x_108);
x_109 = lean_ctor_get(x_98, 8);
lean_inc_ref(x_109);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 lean_ctor_release(x_98, 2);
 lean_ctor_release(x_98, 3);
 lean_ctor_release(x_98, 4);
 lean_ctor_release(x_98, 5);
 lean_ctor_release(x_98, 6);
 lean_ctor_release(x_98, 7);
 lean_ctor_release(x_98, 8);
 x_110 = x_98;
} else {
 lean_dec_ref(x_98);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get_uint64(x_99, sizeof(void*)*1);
x_112 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
x_114 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0;
x_115 = 0;
x_116 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1;
x_117 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set_float(x_117, sizeof(void*)*2, x_114);
lean_ctor_set_float(x_117, sizeof(void*)*2 + 8, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*2 + 16, x_115);
x_118 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2;
x_119 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_95);
lean_ctor_set(x_119, 2, x_118);
lean_inc(x_8);
if (lean_is_scalar(x_101)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_101;
}
lean_ctor_set(x_120, 0, x_8);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_PersistentArray_push___redArg(x_112, x_120);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 1, 8);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set_uint64(x_122, sizeof(void*)*1, x_111);
if (lean_is_scalar(x_110)) {
 x_123 = lean_alloc_ctor(0, 9, 0);
} else {
 x_123 = x_110;
}
lean_ctor_set(x_123, 0, x_102);
lean_ctor_set(x_123, 1, x_103);
lean_ctor_set(x_123, 2, x_104);
lean_ctor_set(x_123, 3, x_105);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set(x_123, 5, x_106);
lean_ctor_set(x_123, 6, x_107);
lean_ctor_set(x_123, 7, x_108);
lean_ctor_set(x_123, 8, x_109);
x_124 = lean_st_ref_set(x_6, x_123, x_100);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inj", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_mkInjEq___closed__2;
x_2 = l_Lean_Meta_Grind_mkInjEq___closed__1;
x_3 = l_Lean_Meta_Grind_mkInjEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_mkInjEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_mkInjEq___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkInjEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
x_13 = lean_st_ref_get(x_2, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 13);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(x_18, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_15, 1, x_16);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_15);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_22, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_27);
lean_dec(x_22);
x_28 = l_Lean_Expr_app___override(x_26, x_1);
x_42 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_28);
x_43 = lean_grind_internalize(x_28, x_24, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = l_Lean_Meta_Grind_mkInjEq___closed__3;
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(x_47, x_8, x_45);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_free_object(x_43);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec_ref(x_48);
x_29 = x_2;
x_30 = x_3;
x_31 = x_4;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_51;
goto block_41;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
lean_inc_ref(x_28);
x_55 = l_Lean_MessageData_ofExpr(x_28);
x_56 = l_Lean_Meta_Grind_mkInjEq___closed__5;
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_56);
lean_ctor_set(x_48, 0, x_55);
lean_inc_ref(x_12);
x_57 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_57);
lean_ctor_set(x_43, 0, x_48);
x_58 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_47, x_43, x_6, x_7, x_8, x_9, x_53);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_29 = x_2;
x_30 = x_3;
x_31 = x_4;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_59;
goto block_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_dec(x_48);
lean_inc_ref(x_28);
x_61 = l_Lean_MessageData_ofExpr(x_28);
x_62 = l_Lean_Meta_Grind_mkInjEq___closed__5;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
lean_inc_ref(x_12);
x_64 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_43, 7);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_63);
x_65 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_47, x_43, x_6, x_7, x_8, x_9, x_60);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_29 = x_2;
x_30 = x_3;
x_31 = x_4;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_66;
goto block_41;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_68 = l_Lean_Meta_Grind_mkInjEq___closed__3;
x_69 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(x_68, x_8, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec_ref(x_69);
x_29 = x_2;
x_30 = x_3;
x_31 = x_4;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_72;
goto block_41;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_74 = x_69;
} else {
 lean_dec_ref(x_69);
 x_74 = lean_box(0);
}
lean_inc_ref(x_28);
x_75 = l_Lean_MessageData_ofExpr(x_28);
x_76 = l_Lean_Meta_Grind_mkInjEq___closed__5;
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_74;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_inc_ref(x_12);
x_78 = l_Lean_MessageData_ofExpr(x_12);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_68, x_79, x_6, x_7, x_8, x_9, x_73);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
x_29 = x_2;
x_30 = x_3;
x_31 = x_4;
x_32 = x_5;
x_33 = x_6;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_81;
goto block_41;
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
block_41:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
lean_inc_ref(x_12);
x_38 = l_Lean_Expr_app___override(x_27, x_12);
x_39 = 0;
x_40 = l_Lean_Meta_Grind_pushEqCore(x_28, x_12, x_38, x_39, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_40;
}
}
else
{
uint8_t x_82; 
lean_dec(x_22);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_23);
if (x_82 == 0)
{
return x_23;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_23, 0);
x_84 = lean_ctor_get(x_23, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_23);
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
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_15, 1);
lean_inc(x_86);
lean_dec(x_15);
x_87 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(x_86, x_11);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_12);
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
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_16);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec_ref(x_87);
x_91 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_16);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_110; lean_object* x_111; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc_ref(x_95);
lean_dec(x_90);
x_96 = l_Lean_Expr_app___override(x_94, x_1);
x_110 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_96);
x_111 = lean_grind_internalize(x_96, x_92, x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_93);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_Lean_Meta_Grind_mkInjEq___closed__3;
x_115 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(x_114, x_8, x_112);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_113);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec_ref(x_115);
x_97 = x_2;
x_98 = x_3;
x_99 = x_4;
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_118;
goto block_109;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
lean_inc_ref(x_96);
x_121 = l_Lean_MessageData_ofExpr(x_96);
x_122 = l_Lean_Meta_Grind_mkInjEq___closed__5;
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(7, 2, 0);
} else {
 x_123 = x_120;
 lean_ctor_set_tag(x_123, 7);
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
lean_inc_ref(x_12);
x_124 = l_Lean_MessageData_ofExpr(x_12);
if (lean_is_scalar(x_113)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_113;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_114, x_125, x_6, x_7, x_8, x_9, x_119);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec_ref(x_126);
x_97 = x_2;
x_98 = x_3;
x_99 = x_4;
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_127;
goto block_109;
}
}
else
{
lean_dec_ref(x_96);
lean_dec_ref(x_95);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_111;
}
block_109:
{
lean_object* x_106; uint8_t x_107; lean_object* x_108; 
lean_inc_ref(x_12);
x_106 = l_Lean_Expr_app___override(x_95, x_12);
x_107 = 0;
x_108 = l_Lean_Meta_Grind_pushEqCore(x_96, x_12, x_106, x_107, x_97, x_98, x_99, x_100, x_101, x_102, x_103, x_104, x_105);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_108;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_90);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_91, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_91, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_130 = x_91;
} else {
 lean_dec_ref(x_91);
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
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_10);
return x_133;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_mkInjEq_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__1___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_Grind_hashPtrExpr_unsafe__1(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.PropagateInj", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.PropagateInj.0.Lean.Meta.Grind.initInjFn.initLeftInv", 84, 84);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(39u);
x_4 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nonempty", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leftInv", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8;
x_3 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leftInv_eq", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12;
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8;
x_3 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_obj_tag(x_1) == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = x_15;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = x_15;
goto block_27;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6;
lean_inc(x_32);
lean_ctor_set(x_28, 0, x_32);
x_34 = l_Lean_mkConst(x_33, x_28);
lean_inc_ref(x_2);
x_35 = l_Lean_mkAppB(x_34, x_2, x_6);
x_36 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10;
lean_inc_ref(x_1);
x_37 = l_Lean_mkConst(x_36, x_1);
lean_inc_ref(x_4);
x_38 = l_Lean_mkApp5(x_37, x_2, x_3, x_4, x_5, x_35);
lean_inc(x_7);
x_39 = l_Lean_Meta_Grind_preprocessLight(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_st_ref_take(x_7, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 13);
lean_inc_ref(x_45);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_44, 13);
lean_dec(x_50);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_45, 1);
x_53 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_54 = l_Lean_Expr_getAppNumArgs(x_41);
lean_inc(x_54);
x_55 = lean_mk_array(x_54, x_53);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_sub(x_54, x_56);
lean_dec(x_54);
lean_inc(x_41);
x_58 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_41, x_55, x_57);
x_59 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_60 = l_Lean_mkConst(x_59, x_1);
x_61 = l_Lean_mkAppN(x_60, x_58);
lean_dec_ref(x_58);
lean_ctor_set(x_43, 1, x_61);
lean_ctor_set(x_43, 0, x_41);
x_62 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_52, x_4, x_43);
lean_ctor_set(x_45, 1, x_62);
x_63 = lean_st_ref_set(x_7, x_44, x_47);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_box(0);
lean_ctor_set(x_39, 1, x_64);
lean_ctor_set(x_39, 0, x_65);
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_66 = lean_ctor_get(x_45, 0);
x_67 = lean_ctor_get(x_45, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_45);
x_68 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_69 = l_Lean_Expr_getAppNumArgs(x_41);
lean_inc(x_69);
x_70 = lean_mk_array(x_69, x_68);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_69, x_71);
lean_dec(x_69);
lean_inc(x_41);
x_73 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_41, x_70, x_72);
x_74 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_75 = l_Lean_mkConst(x_74, x_1);
x_76 = l_Lean_mkAppN(x_75, x_73);
lean_dec_ref(x_73);
lean_ctor_set(x_43, 1, x_76);
lean_ctor_set(x_43, 0, x_41);
x_77 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_67, x_4, x_43);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_44, 13, x_78);
x_79 = lean_st_ref_set(x_7, x_44, x_47);
lean_dec(x_7);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_box(0);
lean_ctor_set(x_39, 1, x_80);
lean_ctor_set(x_39, 0, x_81);
return x_39;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_82 = lean_ctor_get(x_44, 0);
x_83 = lean_ctor_get(x_44, 1);
x_84 = lean_ctor_get(x_44, 2);
x_85 = lean_ctor_get(x_44, 3);
x_86 = lean_ctor_get(x_44, 4);
x_87 = lean_ctor_get(x_44, 5);
x_88 = lean_ctor_get(x_44, 6);
x_89 = lean_ctor_get(x_44, 7);
x_90 = lean_ctor_get_uint8(x_44, sizeof(void*)*17);
x_91 = lean_ctor_get(x_44, 8);
x_92 = lean_ctor_get(x_44, 9);
x_93 = lean_ctor_get(x_44, 10);
x_94 = lean_ctor_get(x_44, 11);
x_95 = lean_ctor_get(x_44, 12);
x_96 = lean_ctor_get(x_44, 14);
x_97 = lean_ctor_get(x_44, 15);
x_98 = lean_ctor_get(x_44, 16);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_44);
x_99 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_100);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_101 = x_45;
} else {
 lean_dec_ref(x_45);
 x_101 = lean_box(0);
}
x_102 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_103 = l_Lean_Expr_getAppNumArgs(x_41);
lean_inc(x_103);
x_104 = lean_mk_array(x_103, x_102);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_103, x_105);
lean_dec(x_103);
lean_inc(x_41);
x_107 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_41, x_104, x_106);
x_108 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_109 = l_Lean_mkConst(x_108, x_1);
x_110 = l_Lean_mkAppN(x_109, x_107);
lean_dec_ref(x_107);
lean_ctor_set(x_43, 1, x_110);
lean_ctor_set(x_43, 0, x_41);
x_111 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_100, x_4, x_43);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_99);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_113, 0, x_82);
lean_ctor_set(x_113, 1, x_83);
lean_ctor_set(x_113, 2, x_84);
lean_ctor_set(x_113, 3, x_85);
lean_ctor_set(x_113, 4, x_86);
lean_ctor_set(x_113, 5, x_87);
lean_ctor_set(x_113, 6, x_88);
lean_ctor_set(x_113, 7, x_89);
lean_ctor_set(x_113, 8, x_91);
lean_ctor_set(x_113, 9, x_92);
lean_ctor_set(x_113, 10, x_93);
lean_ctor_set(x_113, 11, x_94);
lean_ctor_set(x_113, 12, x_95);
lean_ctor_set(x_113, 13, x_112);
lean_ctor_set(x_113, 14, x_96);
lean_ctor_set(x_113, 15, x_97);
lean_ctor_set(x_113, 16, x_98);
lean_ctor_set_uint8(x_113, sizeof(void*)*17, x_90);
x_114 = lean_st_ref_set(x_7, x_113, x_47);
lean_dec(x_7);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = lean_box(0);
lean_ctor_set(x_39, 1, x_115);
lean_ctor_set(x_39, 0, x_116);
return x_39;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_117 = lean_ctor_get(x_43, 1);
lean_inc(x_117);
lean_dec(x_43);
x_118 = lean_ctor_get(x_44, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_44, 1);
lean_inc_ref(x_119);
x_120 = lean_ctor_get(x_44, 2);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_44, 3);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_44, 4);
lean_inc_ref(x_122);
x_123 = lean_ctor_get(x_44, 5);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_44, 6);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_44, 7);
lean_inc_ref(x_125);
x_126 = lean_ctor_get_uint8(x_44, sizeof(void*)*17);
x_127 = lean_ctor_get(x_44, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_44, 9);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_44, 10);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_44, 11);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_44, 12);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_44, 14);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_44, 15);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_44, 16);
lean_inc_ref(x_134);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 lean_ctor_release(x_44, 6);
 lean_ctor_release(x_44, 7);
 lean_ctor_release(x_44, 8);
 lean_ctor_release(x_44, 9);
 lean_ctor_release(x_44, 10);
 lean_ctor_release(x_44, 11);
 lean_ctor_release(x_44, 12);
 lean_ctor_release(x_44, 13);
 lean_ctor_release(x_44, 14);
 lean_ctor_release(x_44, 15);
 lean_ctor_release(x_44, 16);
 x_135 = x_44;
} else {
 lean_dec_ref(x_44);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_137);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_138 = x_45;
} else {
 lean_dec_ref(x_45);
 x_138 = lean_box(0);
}
x_139 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_140 = l_Lean_Expr_getAppNumArgs(x_41);
lean_inc(x_140);
x_141 = lean_mk_array(x_140, x_139);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_sub(x_140, x_142);
lean_dec(x_140);
lean_inc(x_41);
x_144 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_41, x_141, x_143);
x_145 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_146 = l_Lean_mkConst(x_145, x_1);
x_147 = l_Lean_mkAppN(x_146, x_144);
lean_dec_ref(x_144);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_41);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_137, x_4, x_148);
if (lean_is_scalar(x_138)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_138;
}
lean_ctor_set(x_150, 0, x_136);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_135)) {
 x_151 = lean_alloc_ctor(0, 17, 1);
} else {
 x_151 = x_135;
}
lean_ctor_set(x_151, 0, x_118);
lean_ctor_set(x_151, 1, x_119);
lean_ctor_set(x_151, 2, x_120);
lean_ctor_set(x_151, 3, x_121);
lean_ctor_set(x_151, 4, x_122);
lean_ctor_set(x_151, 5, x_123);
lean_ctor_set(x_151, 6, x_124);
lean_ctor_set(x_151, 7, x_125);
lean_ctor_set(x_151, 8, x_127);
lean_ctor_set(x_151, 9, x_128);
lean_ctor_set(x_151, 10, x_129);
lean_ctor_set(x_151, 11, x_130);
lean_ctor_set(x_151, 12, x_131);
lean_ctor_set(x_151, 13, x_150);
lean_ctor_set(x_151, 14, x_132);
lean_ctor_set(x_151, 15, x_133);
lean_ctor_set(x_151, 16, x_134);
lean_ctor_set_uint8(x_151, sizeof(void*)*17, x_126);
x_152 = lean_st_ref_set(x_7, x_151, x_117);
lean_dec(x_7);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = lean_box(0);
lean_ctor_set(x_39, 1, x_153);
lean_ctor_set(x_39, 0, x_154);
return x_39;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_155 = lean_ctor_get(x_39, 0);
x_156 = lean_ctor_get(x_39, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_39);
x_157 = lean_st_ref_take(x_7, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 13);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_158, 1);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_158, 2);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_158, 3);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_158, 4);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_158, 5);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_158, 6);
lean_inc_ref(x_168);
x_169 = lean_ctor_get(x_158, 7);
lean_inc_ref(x_169);
x_170 = lean_ctor_get_uint8(x_158, sizeof(void*)*17);
x_171 = lean_ctor_get(x_158, 8);
lean_inc(x_171);
x_172 = lean_ctor_get(x_158, 9);
lean_inc_ref(x_172);
x_173 = lean_ctor_get(x_158, 10);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_158, 11);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_158, 12);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_158, 14);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_158, 15);
lean_inc_ref(x_177);
x_178 = lean_ctor_get(x_158, 16);
lean_inc_ref(x_178);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 lean_ctor_release(x_158, 4);
 lean_ctor_release(x_158, 5);
 lean_ctor_release(x_158, 6);
 lean_ctor_release(x_158, 7);
 lean_ctor_release(x_158, 8);
 lean_ctor_release(x_158, 9);
 lean_ctor_release(x_158, 10);
 lean_ctor_release(x_158, 11);
 lean_ctor_release(x_158, 12);
 lean_ctor_release(x_158, 13);
 lean_ctor_release(x_158, 14);
 lean_ctor_release(x_158, 15);
 lean_ctor_release(x_158, 16);
 x_179 = x_158;
} else {
 lean_dec_ref(x_158);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_159, 1);
lean_inc_ref(x_181);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_182 = x_159;
} else {
 lean_dec_ref(x_159);
 x_182 = lean_box(0);
}
x_183 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_184 = l_Lean_Expr_getAppNumArgs(x_155);
lean_inc(x_184);
x_185 = lean_mk_array(x_184, x_183);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_sub(x_184, x_186);
lean_dec(x_184);
lean_inc(x_155);
x_188 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_155, x_185, x_187);
x_189 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_190 = l_Lean_mkConst(x_189, x_1);
x_191 = l_Lean_mkAppN(x_190, x_188);
lean_dec_ref(x_188);
if (lean_is_scalar(x_161)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_161;
}
lean_ctor_set(x_192, 0, x_155);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_181, x_4, x_192);
if (lean_is_scalar(x_182)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_182;
}
lean_ctor_set(x_194, 0, x_180);
lean_ctor_set(x_194, 1, x_193);
if (lean_is_scalar(x_179)) {
 x_195 = lean_alloc_ctor(0, 17, 1);
} else {
 x_195 = x_179;
}
lean_ctor_set(x_195, 0, x_162);
lean_ctor_set(x_195, 1, x_163);
lean_ctor_set(x_195, 2, x_164);
lean_ctor_set(x_195, 3, x_165);
lean_ctor_set(x_195, 4, x_166);
lean_ctor_set(x_195, 5, x_167);
lean_ctor_set(x_195, 6, x_168);
lean_ctor_set(x_195, 7, x_169);
lean_ctor_set(x_195, 8, x_171);
lean_ctor_set(x_195, 9, x_172);
lean_ctor_set(x_195, 10, x_173);
lean_ctor_set(x_195, 11, x_174);
lean_ctor_set(x_195, 12, x_175);
lean_ctor_set(x_195, 13, x_194);
lean_ctor_set(x_195, 14, x_176);
lean_ctor_set(x_195, 15, x_177);
lean_ctor_set(x_195, 16, x_178);
lean_ctor_set_uint8(x_195, sizeof(void*)*17, x_170);
x_196 = lean_st_ref_set(x_7, x_195, x_160);
lean_dec(x_7);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_39);
if (x_200 == 0)
{
return x_39;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_39, 0);
x_202 = lean_ctor_get(x_39, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_39);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_free_object(x_28);
lean_dec_ref(x_30);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = x_15;
goto block_27;
}
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_28, 1);
lean_inc(x_204);
lean_dec(x_28);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_205 = lean_ctor_get(x_1, 0);
x_206 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6;
lean_inc(x_205);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_204);
x_208 = l_Lean_mkConst(x_206, x_207);
lean_inc_ref(x_2);
x_209 = l_Lean_mkAppB(x_208, x_2, x_6);
x_210 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10;
lean_inc_ref(x_1);
x_211 = l_Lean_mkConst(x_210, x_1);
lean_inc_ref(x_4);
x_212 = l_Lean_mkApp5(x_211, x_2, x_3, x_4, x_5, x_209);
lean_inc(x_7);
x_213 = l_Lean_Meta_Grind_preprocessLight(x_212, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_216 = x_213;
} else {
 lean_dec_ref(x_213);
 x_216 = lean_box(0);
}
x_217 = lean_st_ref_take(x_7, x_215);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_218, 13);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_221 = x_217;
} else {
 lean_dec_ref(x_217);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_218, 1);
lean_inc_ref(x_223);
x_224 = lean_ctor_get(x_218, 2);
lean_inc_ref(x_224);
x_225 = lean_ctor_get(x_218, 3);
lean_inc_ref(x_225);
x_226 = lean_ctor_get(x_218, 4);
lean_inc_ref(x_226);
x_227 = lean_ctor_get(x_218, 5);
lean_inc_ref(x_227);
x_228 = lean_ctor_get(x_218, 6);
lean_inc_ref(x_228);
x_229 = lean_ctor_get(x_218, 7);
lean_inc_ref(x_229);
x_230 = lean_ctor_get_uint8(x_218, sizeof(void*)*17);
x_231 = lean_ctor_get(x_218, 8);
lean_inc(x_231);
x_232 = lean_ctor_get(x_218, 9);
lean_inc_ref(x_232);
x_233 = lean_ctor_get(x_218, 10);
lean_inc_ref(x_233);
x_234 = lean_ctor_get(x_218, 11);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_218, 12);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_218, 14);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_218, 15);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_218, 16);
lean_inc_ref(x_238);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 lean_ctor_release(x_218, 5);
 lean_ctor_release(x_218, 6);
 lean_ctor_release(x_218, 7);
 lean_ctor_release(x_218, 8);
 lean_ctor_release(x_218, 9);
 lean_ctor_release(x_218, 10);
 lean_ctor_release(x_218, 11);
 lean_ctor_release(x_218, 12);
 lean_ctor_release(x_218, 13);
 lean_ctor_release(x_218, 14);
 lean_ctor_release(x_218, 15);
 lean_ctor_release(x_218, 16);
 x_239 = x_218;
} else {
 lean_dec_ref(x_218);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_219, 0);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_219, 1);
lean_inc_ref(x_241);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_242 = x_219;
} else {
 lean_dec_ref(x_219);
 x_242 = lean_box(0);
}
x_243 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11;
x_244 = l_Lean_Expr_getAppNumArgs(x_214);
lean_inc(x_244);
x_245 = lean_mk_array(x_244, x_243);
x_246 = lean_unsigned_to_nat(1u);
x_247 = lean_nat_sub(x_244, x_246);
lean_dec(x_244);
lean_inc(x_214);
x_248 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_214, x_245, x_247);
x_249 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13;
x_250 = l_Lean_mkConst(x_249, x_1);
x_251 = l_Lean_mkAppN(x_250, x_248);
lean_dec_ref(x_248);
if (lean_is_scalar(x_221)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_221;
}
lean_ctor_set(x_252, 0, x_214);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1___redArg(x_241, x_4, x_252);
if (lean_is_scalar(x_242)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_242;
}
lean_ctor_set(x_254, 0, x_240);
lean_ctor_set(x_254, 1, x_253);
if (lean_is_scalar(x_239)) {
 x_255 = lean_alloc_ctor(0, 17, 1);
} else {
 x_255 = x_239;
}
lean_ctor_set(x_255, 0, x_222);
lean_ctor_set(x_255, 1, x_223);
lean_ctor_set(x_255, 2, x_224);
lean_ctor_set(x_255, 3, x_225);
lean_ctor_set(x_255, 4, x_226);
lean_ctor_set(x_255, 5, x_227);
lean_ctor_set(x_255, 6, x_228);
lean_ctor_set(x_255, 7, x_229);
lean_ctor_set(x_255, 8, x_231);
lean_ctor_set(x_255, 9, x_232);
lean_ctor_set(x_255, 10, x_233);
lean_ctor_set(x_255, 11, x_234);
lean_ctor_set(x_255, 12, x_235);
lean_ctor_set(x_255, 13, x_254);
lean_ctor_set(x_255, 14, x_236);
lean_ctor_set(x_255, 15, x_237);
lean_ctor_set(x_255, 16, x_238);
lean_ctor_set_uint8(x_255, sizeof(void*)*17, x_230);
x_256 = lean_st_ref_set(x_7, x_255, x_220);
lean_dec(x_7);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_box(0);
if (lean_is_scalar(x_216)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_216;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_260 = lean_ctor_get(x_213, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_213, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_262 = x_213;
} else {
 lean_dec_ref(x_213);
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
else
{
lean_dec_ref(x_204);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_11;
x_21 = x_12;
x_22 = x_13;
x_23 = x_14;
x_24 = x_15;
goto block_27;
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3;
x_26 = l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0(x_25, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = lean_box(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_39; uint8_t x_50; 
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec_ref(x_6);
x_50 = l_Lean_Expr_isApp(x_19);
if (x_50 == 0)
{
x_39 = x_50;
goto block_49;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_appFn_x21(x_19);
x_52 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_51, x_4);
lean_dec_ref(x_51);
x_39 = x_52;
goto block_49;
}
block_38:
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_mkInjEq(x_19, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec_ref(x_31);
x_6 = x_20;
x_7 = x_21;
x_16 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
block_49:
{
if (x_39 == 0)
{
lean_dec(x_19);
x_6 = x_20;
goto _start;
}
else
{
if (x_7 == 0)
{
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
x_29 = x_15;
x_30 = x_16;
goto block_38;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Expr_appArg_x21(x_19);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_42 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv(x_1, x_2, x_3, x_4, x_5, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = 0;
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = x_44;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_12;
x_27 = x_13;
x_28 = x_14;
x_29 = x_15;
x_30 = x_43;
goto block_38;
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l_Lean_instBEqHeadIndex_beq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_instBEqHeadIndex_beq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_instBEqHeadIndex_beq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_HeadIndex_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_34; 
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_ctor_get(x_16, 6);
lean_inc_ref(x_18);
lean_dec(x_16);
lean_inc_ref(x_4);
x_19 = l_Lean_Expr_toHeadIndex(x_4);
x_20 = 1;
x_34 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(x_18, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_21 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_21 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_22; 
x_22 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_21, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_7);
x_18 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_8);
x_20 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Function", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Injective", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_11 = x_10;
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
x_11 = x_10;
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc_ref(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
if (x_23 == 0)
{
lean_dec_ref(x_21);
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
x_11 = x_10;
goto block_14;
}
else
{
lean_object* x_24; 
lean_inc_ref(x_1);
x_24 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec_ref(x_21);
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
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_58; uint8_t x_59; 
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_dec_ref(x_24);
x_34 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_15);
x_35 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_35);
lean_dec_ref(x_17);
x_36 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_19);
lean_inc_ref(x_34);
x_58 = l_Lean_Expr_eta(x_34);
x_59 = l___private_Lean_Meta_Tactic_Grind_ExprPtr_0__Lean_Meta_Grind_isSameExpr_unsafe__1(x_34, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec_ref(x_34);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l_Lean_Meta_Grind_preprocessLight(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_61);
x_67 = lean_grind_internalize(x_61, x_64, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_37 = x_61;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_68;
goto block_57;
}
else
{
lean_dec(x_61);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_67;
}
}
else
{
uint8_t x_69; 
lean_dec(x_61);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
return x_63;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
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
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_60);
if (x_73 == 0)
{
return x_60;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_dec_ref(x_58);
x_37 = x_34;
x_38 = x_2;
x_39 = x_3;
x_40 = x_4;
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = x_9;
x_46 = x_33;
goto block_57;
}
block_57:
{
lean_object* x_47; 
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Lean_Expr_constLevels_x21(x_21);
lean_dec_ref(x_21);
x_51 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_48);
x_52 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(x_50, x_36, x_35, x_37, x_51, x_38, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_49);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
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
uint8_t x_77; 
lean_dec_ref(x_21);
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
x_77 = !lean_is_exclusive(x_24);
if (x_77 == 0)
{
return x_24;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_24, 0);
x_79 = lean_ctor_get(x_24, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_24);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1____x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
x_3 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Injective(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_mkInjEq_spec__0_spec__0___redArg___closed__1();
l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__1);
l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_mkInjEq_spec__4___redArg___closed__2);
l_Lean_Meta_Grind_mkInjEq___closed__0 = _init_l_Lean_Meta_Grind_mkInjEq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__0);
l_Lean_Meta_Grind_mkInjEq___closed__1 = _init_l_Lean_Meta_Grind_mkInjEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__1);
l_Lean_Meta_Grind_mkInjEq___closed__2 = _init_l_Lean_Meta_Grind_mkInjEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__2);
l_Lean_Meta_Grind_mkInjEq___closed__3 = _init_l_Lean_Meta_Grind_mkInjEq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__3);
l_Lean_Meta_Grind_mkInjEq___closed__4 = _init_l_Lean_Meta_Grind_mkInjEq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__4);
l_Lean_Meta_Grind_mkInjEq___closed__5 = _init_l_Lean_Meta_Grind_mkInjEq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_mkInjEq___closed__5);
l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__0___closed__0);
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv_spec__1_spec__1___redArg___closed__0);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__0);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__1);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__2);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__3);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__4);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__5);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__6);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__7);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__8);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__9);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__10);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__11);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__12);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_initLeftInv___closed__13);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1);
l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1____x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
