// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.OrHull
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Std.Data.TreeMap.Basic import Std.Data.TreeSet.Basic import Lean.Meta.Tactic.Grind.Formula import Lean.Util.MonadCache import Lean.Meta.NatInstTesters import Lean.Meta.IntInstTesters import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_Bool_toLBool(uint8_t);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_instInhabitedAdmission;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__3_value),LEAN_SCALAR_PTR_LITERAL(105, 164, 65, 191, 194, 192, 188, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 9, 233, 146, 238, 75, 109, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__1(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___boxed(lean_object**);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__3, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2_spec__5(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__1_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__2_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___boxed, .m_arity = 15, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___boxed(lean_object**);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__1);
v___x_5_ = lean_box(1);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
return v___x_7_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default;
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(lean_object* v_k_9_, lean_object* v_v_10_, lean_object* v_t_11_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_size_12_; lean_object* v_k_13_; lean_object* v_v_14_; lean_object* v_l_15_; lean_object* v_r_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_297_; 
v_size_12_ = lean_ctor_get(v_t_11_, 0);
v_k_13_ = lean_ctor_get(v_t_11_, 1);
v_v_14_ = lean_ctor_get(v_t_11_, 2);
v_l_15_ = lean_ctor_get(v_t_11_, 3);
v_r_16_ = lean_ctor_get(v_t_11_, 4);
v_isSharedCheck_297_ = !lean_is_exclusive(v_t_11_);
if (v_isSharedCheck_297_ == 0)
{
v___x_18_ = v_t_11_;
v_isShared_19_ = v_isSharedCheck_297_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_r_16_);
lean_inc(v_l_15_);
lean_inc(v_v_14_);
lean_inc(v_k_13_);
lean_inc(v_size_12_);
lean_dec(v_t_11_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_297_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
uint8_t v___x_20_; 
v___x_20_ = lean_int_dec_lt(v_k_9_, v_k_13_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = lean_int_dec_eq(v_k_9_, v_k_13_);
if (v___x_21_ == 0)
{
lean_object* v_impl_22_; lean_object* v___x_23_; 
lean_dec(v_size_12_);
v_impl_22_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(v_k_9_, v_v_10_, v_r_16_);
v___x_23_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_15_) == 0)
{
lean_object* v_size_24_; lean_object* v_size_25_; lean_object* v_k_26_; lean_object* v_v_27_; lean_object* v_l_28_; lean_object* v_r_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_size_24_ = lean_ctor_get(v_l_15_, 0);
v_size_25_ = lean_ctor_get(v_impl_22_, 0);
v_k_26_ = lean_ctor_get(v_impl_22_, 1);
v_v_27_ = lean_ctor_get(v_impl_22_, 2);
v_l_28_ = lean_ctor_get(v_impl_22_, 3);
lean_inc(v_l_28_);
v_r_29_ = lean_ctor_get(v_impl_22_, 4);
v___x_30_ = lean_unsigned_to_nat(3u);
v___x_31_ = lean_nat_mul(v___x_30_, v_size_24_);
v___x_32_ = lean_nat_dec_lt(v___x_31_, v_size_25_);
lean_dec(v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
lean_dec(v_l_28_);
v___x_33_ = lean_nat_add(v___x_23_, v_size_24_);
v___x_34_ = lean_nat_add(v___x_33_, v_size_25_);
lean_dec(v___x_33_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_impl_22_);
lean_ctor_set(v___x_18_, 0, v___x_34_);
v___x_36_ = v___x_18_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_37_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_37_, 4, v_impl_22_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
else
{
lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_101_; 
lean_inc(v_r_29_);
lean_inc(v_v_27_);
lean_inc(v_k_26_);
lean_inc(v_size_25_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; lean_object* v_unused_106_; 
v_unused_102_ = lean_ctor_get(v_impl_22_, 4);
lean_dec(v_unused_102_);
v_unused_103_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_impl_22_, 2);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_impl_22_, 1);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_106_);
v___x_39_ = v_impl_22_;
v_isShared_40_ = v_isSharedCheck_101_;
goto v_resetjp_38_;
}
else
{
lean_dec(v_impl_22_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_101_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_size_41_; lean_object* v_k_42_; lean_object* v_v_43_; lean_object* v_l_44_; lean_object* v_r_45_; lean_object* v_size_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_size_41_ = lean_ctor_get(v_l_28_, 0);
v_k_42_ = lean_ctor_get(v_l_28_, 1);
v_v_43_ = lean_ctor_get(v_l_28_, 2);
v_l_44_ = lean_ctor_get(v_l_28_, 3);
v_r_45_ = lean_ctor_get(v_l_28_, 4);
v_size_46_ = lean_ctor_get(v_r_29_, 0);
v___x_47_ = lean_unsigned_to_nat(2u);
v___x_48_ = lean_nat_mul(v___x_47_, v_size_46_);
v___x_49_ = lean_nat_dec_lt(v_size_41_, v___x_48_);
lean_dec(v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_77_; 
lean_inc(v_r_45_);
lean_inc(v_l_44_);
lean_inc(v_v_43_);
lean_inc(v_k_42_);
v_isSharedCheck_77_ = !lean_is_exclusive(v_l_28_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; lean_object* v_unused_79_; lean_object* v_unused_80_; lean_object* v_unused_81_; lean_object* v_unused_82_; 
v_unused_78_ = lean_ctor_get(v_l_28_, 4);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_l_28_, 3);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v_l_28_, 2);
lean_dec(v_unused_80_);
v_unused_81_ = lean_ctor_get(v_l_28_, 1);
lean_dec(v_unused_81_);
v_unused_82_ = lean_ctor_get(v_l_28_, 0);
lean_dec(v_unused_82_);
v___x_51_ = v_l_28_;
v_isShared_52_ = v_isSharedCheck_77_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_l_28_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_77_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___y_56_; lean_object* v___y_57_; lean_object* v___y_58_; lean_object* v___y_67_; 
v___x_53_ = lean_nat_add(v___x_23_, v_size_24_);
v___x_54_ = lean_nat_add(v___x_53_, v_size_25_);
lean_dec(v_size_25_);
if (lean_obj_tag(v_l_44_) == 0)
{
lean_object* v_size_75_; 
v_size_75_ = lean_ctor_get(v_l_44_, 0);
lean_inc(v_size_75_);
v___y_67_ = v_size_75_;
goto v___jp_66_;
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___y_67_ = v___x_76_;
goto v___jp_66_;
}
v___jp_55_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_nat_add(v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec(v___y_57_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 4, v_r_29_);
lean_ctor_set(v___x_51_, 3, v_r_45_);
lean_ctor_set(v___x_51_, 2, v_v_27_);
lean_ctor_set(v___x_51_, 1, v_k_26_);
lean_ctor_set(v___x_51_, 0, v___x_59_);
v___x_61_ = v___x_51_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_65_, 3, v_r_45_);
lean_ctor_set(v_reuseFailAlloc_65_, 4, v_r_29_);
v___x_61_ = v_reuseFailAlloc_65_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_63_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 4, v___x_61_);
lean_ctor_set(v___x_39_, 3, v___y_56_);
lean_ctor_set(v___x_39_, 2, v_v_43_);
lean_ctor_set(v___x_39_, 1, v_k_42_);
lean_ctor_set(v___x_39_, 0, v___x_54_);
v___x_63_ = v___x_39_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_k_42_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_v_43_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v___y_56_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_nat_add(v___x_53_, v___y_67_);
lean_dec(v___y_67_);
lean_dec(v___x_53_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_l_44_);
lean_ctor_set(v___x_18_, 0, v___x_68_);
v___x_70_ = v___x_18_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_74_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_74_, 4, v_l_44_);
v___x_70_ = v_reuseFailAlloc_74_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_nat_add(v___x_23_, v_size_46_);
if (lean_obj_tag(v_r_45_) == 0)
{
lean_object* v_size_72_; 
v_size_72_ = lean_ctor_get(v_r_45_, 0);
lean_inc(v_size_72_);
v___y_56_ = v___x_70_;
v___y_57_ = v___x_71_;
v___y_58_ = v_size_72_;
goto v___jp_55_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___y_56_ = v___x_70_;
v___y_57_ = v___x_71_;
v___y_58_ = v___x_73_;
goto v___jp_55_;
}
}
}
}
}
else
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
lean_del_object(v___x_18_);
v___x_83_ = lean_nat_add(v___x_23_, v_size_24_);
v___x_84_ = lean_nat_add(v___x_83_, v_size_25_);
lean_dec(v_size_25_);
v___x_85_ = lean_nat_add(v___x_83_, v_size_41_);
lean_dec(v___x_83_);
lean_inc_ref(v_l_15_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 4, v_l_28_);
lean_ctor_set(v___x_39_, 3, v_l_15_);
lean_ctor_set(v___x_39_, 2, v_v_14_);
lean_ctor_set(v___x_39_, 1, v_k_13_);
lean_ctor_set(v___x_39_, 0, v___x_85_);
v___x_87_ = v___x_39_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v_l_28_);
v___x_87_ = v_reuseFailAlloc_100_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
v_isSharedCheck_94_ = !lean_is_exclusive(v_l_15_);
if (v_isSharedCheck_94_ == 0)
{
lean_object* v_unused_95_; lean_object* v_unused_96_; lean_object* v_unused_97_; lean_object* v_unused_98_; lean_object* v_unused_99_; 
v_unused_95_ = lean_ctor_get(v_l_15_, 4);
lean_dec(v_unused_95_);
v_unused_96_ = lean_ctor_get(v_l_15_, 3);
lean_dec(v_unused_96_);
v_unused_97_ = lean_ctor_get(v_l_15_, 2);
lean_dec(v_unused_97_);
v_unused_98_ = lean_ctor_get(v_l_15_, 1);
lean_dec(v_unused_98_);
v_unused_99_ = lean_ctor_get(v_l_15_, 0);
lean_dec(v_unused_99_);
v___x_89_ = v_l_15_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_dec(v_l_15_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 4, v_r_29_);
lean_ctor_set(v___x_89_, 3, v___x_87_);
lean_ctor_set(v___x_89_, 2, v_v_27_);
lean_ctor_set(v___x_89_, 1, v_k_26_);
lean_ctor_set(v___x_89_, 0, v___x_84_);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v_k_26_);
lean_ctor_set(v_reuseFailAlloc_93_, 2, v_v_27_);
lean_ctor_set(v_reuseFailAlloc_93_, 3, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_93_, 4, v_r_29_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_107_; 
v_l_107_ = lean_ctor_get(v_impl_22_, 3);
lean_inc(v_l_107_);
if (lean_obj_tag(v_l_107_) == 0)
{
lean_object* v_r_108_; lean_object* v_k_109_; lean_object* v_v_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_133_; 
v_r_108_ = lean_ctor_get(v_impl_22_, 4);
v_k_109_ = lean_ctor_get(v_impl_22_, 1);
v_v_110_ = lean_ctor_get(v_impl_22_, 2);
v_isSharedCheck_133_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_133_ == 0)
{
lean_object* v_unused_134_; lean_object* v_unused_135_; 
v_unused_134_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_134_);
v_unused_135_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_135_);
v___x_112_ = v_impl_22_;
v_isShared_113_ = v_isSharedCheck_133_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_r_108_);
lean_inc(v_v_110_);
lean_inc(v_k_109_);
lean_dec(v_impl_22_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_133_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_k_114_; lean_object* v_v_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_129_; 
v_k_114_ = lean_ctor_get(v_l_107_, 1);
v_v_115_ = lean_ctor_get(v_l_107_, 2);
v_isSharedCheck_129_ = !lean_is_exclusive(v_l_107_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_130_ = lean_ctor_get(v_l_107_, 4);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_l_107_, 3);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v_l_107_, 0);
lean_dec(v_unused_132_);
v___x_117_ = v_l_107_;
v_isShared_118_ = v_isSharedCheck_129_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_v_115_);
lean_inc(v_k_114_);
lean_dec(v_l_107_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_129_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_108_, 2);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 4, v_r_108_);
lean_ctor_set(v___x_117_, 3, v_r_108_);
lean_ctor_set(v___x_117_, 2, v_v_14_);
lean_ctor_set(v___x_117_, 1, v_k_13_);
lean_ctor_set(v___x_117_, 0, v___x_23_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_128_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_128_, 3, v_r_108_);
lean_ctor_set(v_reuseFailAlloc_128_, 4, v_r_108_);
v___x_121_ = v_reuseFailAlloc_128_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
lean_inc(v_r_108_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 3, v_r_108_);
lean_ctor_set(v___x_112_, 0, v___x_23_);
v___x_123_ = v___x_112_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_k_109_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_v_110_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_r_108_);
lean_ctor_set(v_reuseFailAlloc_127_, 4, v_r_108_);
v___x_123_ = v_reuseFailAlloc_127_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_125_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_123_);
lean_ctor_set(v___x_18_, 3, v___x_121_);
lean_ctor_set(v___x_18_, 2, v_v_115_);
lean_ctor_set(v___x_18_, 1, v_k_114_);
lean_ctor_set(v___x_18_, 0, v___x_119_);
v___x_125_ = v___x_18_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_k_114_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_v_115_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_126_, 4, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
}
else
{
lean_object* v_r_136_; 
v_r_136_ = lean_ctor_get(v_impl_22_, 4);
lean_inc(v_r_136_);
if (lean_obj_tag(v_r_136_) == 0)
{
lean_object* v_k_137_; lean_object* v_v_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_149_; 
v_k_137_ = lean_ctor_get(v_impl_22_, 1);
v_v_138_ = lean_ctor_get(v_impl_22_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v_impl_22_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; lean_object* v_unused_151_; lean_object* v_unused_152_; 
v_unused_150_ = lean_ctor_get(v_impl_22_, 4);
lean_dec(v_unused_150_);
v_unused_151_ = lean_ctor_get(v_impl_22_, 3);
lean_dec(v_unused_151_);
v_unused_152_ = lean_ctor_get(v_impl_22_, 0);
lean_dec(v_unused_152_);
v___x_140_ = v_impl_22_;
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_v_138_);
lean_inc(v_k_137_);
lean_dec(v_impl_22_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_149_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_unsigned_to_nat(3u);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 4, v_l_107_);
lean_ctor_set(v___x_140_, 2, v_v_14_);
lean_ctor_set(v___x_140_, 1, v_k_13_);
lean_ctor_set(v___x_140_, 0, v___x_23_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_l_107_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_l_107_);
v___x_144_ = v_reuseFailAlloc_148_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v___x_146_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_r_136_);
lean_ctor_set(v___x_18_, 3, v___x_144_);
lean_ctor_set(v___x_18_, 2, v_v_138_);
lean_ctor_set(v___x_18_, 1, v_k_137_);
lean_ctor_set(v___x_18_, 0, v___x_142_);
v___x_146_ = v___x_18_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v_k_137_);
lean_ctor_set(v_reuseFailAlloc_147_, 2, v_v_138_);
lean_ctor_set(v_reuseFailAlloc_147_, 3, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_147_, 4, v_r_136_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
else
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(2u);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_impl_22_);
lean_ctor_set(v___x_18_, 3, v_r_136_);
lean_ctor_set(v___x_18_, 0, v___x_153_);
v___x_155_ = v___x_18_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_r_136_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_impl_22_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
else
{
lean_object* v___x_158_; 
lean_dec(v_v_14_);
lean_dec(v_k_13_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 2, v_v_10_);
lean_ctor_set(v___x_18_, 1, v_k_9_);
v___x_158_ = v___x_18_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_size_12_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_k_9_);
lean_ctor_set(v_reuseFailAlloc_159_, 2, v_v_10_);
lean_ctor_set(v_reuseFailAlloc_159_, 3, v_l_15_);
lean_ctor_set(v_reuseFailAlloc_159_, 4, v_r_16_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_impl_160_; lean_object* v___x_161_; 
lean_dec(v_size_12_);
v_impl_160_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(v_k_9_, v_v_10_, v_l_15_);
v___x_161_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_16_) == 0)
{
lean_object* v_size_162_; lean_object* v_size_163_; lean_object* v_k_164_; lean_object* v_v_165_; lean_object* v_l_166_; lean_object* v_r_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_size_162_ = lean_ctor_get(v_r_16_, 0);
v_size_163_ = lean_ctor_get(v_impl_160_, 0);
v_k_164_ = lean_ctor_get(v_impl_160_, 1);
v_v_165_ = lean_ctor_get(v_impl_160_, 2);
v_l_166_ = lean_ctor_get(v_impl_160_, 3);
v_r_167_ = lean_ctor_get(v_impl_160_, 4);
lean_inc(v_r_167_);
v___x_168_ = lean_unsigned_to_nat(3u);
v___x_169_ = lean_nat_mul(v___x_168_, v_size_162_);
v___x_170_ = lean_nat_dec_lt(v___x_169_, v_size_163_);
lean_dec(v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec(v_r_167_);
v___x_171_ = lean_nat_add(v___x_161_, v_size_163_);
v___x_172_ = lean_nat_add(v___x_171_, v_size_162_);
lean_dec(v___x_171_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 3, v_impl_160_);
lean_ctor_set(v___x_18_, 0, v___x_172_);
v___x_174_ = v___x_18_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_175_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_175_, 3, v_impl_160_);
lean_ctor_set(v_reuseFailAlloc_175_, 4, v_r_16_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_241_; 
lean_inc(v_l_166_);
lean_inc(v_v_165_);
lean_inc(v_k_164_);
lean_inc(v_size_163_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_impl_160_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_242_ = lean_ctor_get(v_impl_160_, 4);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_impl_160_, 3);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_impl_160_, 2);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_impl_160_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_impl_160_, 0);
lean_dec(v_unused_246_);
v___x_177_ = v_impl_160_;
v_isShared_178_ = v_isSharedCheck_241_;
goto v_resetjp_176_;
}
else
{
lean_dec(v_impl_160_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_241_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_size_179_; lean_object* v_size_180_; lean_object* v_k_181_; lean_object* v_v_182_; lean_object* v_l_183_; lean_object* v_r_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_size_179_ = lean_ctor_get(v_l_166_, 0);
v_size_180_ = lean_ctor_get(v_r_167_, 0);
v_k_181_ = lean_ctor_get(v_r_167_, 1);
v_v_182_ = lean_ctor_get(v_r_167_, 2);
v_l_183_ = lean_ctor_get(v_r_167_, 3);
v_r_184_ = lean_ctor_get(v_r_167_, 4);
v___x_185_ = lean_unsigned_to_nat(2u);
v___x_186_ = lean_nat_mul(v___x_185_, v_size_179_);
v___x_187_ = lean_nat_dec_lt(v_size_180_, v___x_186_);
lean_dec(v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_216_; 
lean_inc(v_r_184_);
lean_inc(v_l_183_);
lean_inc(v_v_182_);
lean_inc(v_k_181_);
v_isSharedCheck_216_ = !lean_is_exclusive(v_r_167_);
if (v_isSharedCheck_216_ == 0)
{
lean_object* v_unused_217_; lean_object* v_unused_218_; lean_object* v_unused_219_; lean_object* v_unused_220_; lean_object* v_unused_221_; 
v_unused_217_ = lean_ctor_get(v_r_167_, 4);
lean_dec(v_unused_217_);
v_unused_218_ = lean_ctor_get(v_r_167_, 3);
lean_dec(v_unused_218_);
v_unused_219_ = lean_ctor_get(v_r_167_, 2);
lean_dec(v_unused_219_);
v_unused_220_ = lean_ctor_get(v_r_167_, 1);
lean_dec(v_unused_220_);
v_unused_221_ = lean_ctor_get(v_r_167_, 0);
lean_dec(v_unused_221_);
v___x_189_ = v_r_167_;
v_isShared_190_ = v_isSharedCheck_216_;
goto v_resetjp_188_;
}
else
{
lean_dec(v_r_167_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_216_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___x_204_; lean_object* v___y_206_; 
v___x_191_ = lean_nat_add(v___x_161_, v_size_163_);
lean_dec(v_size_163_);
v___x_192_ = lean_nat_add(v___x_191_, v_size_162_);
lean_dec(v___x_191_);
v___x_204_ = lean_nat_add(v___x_161_, v_size_179_);
if (lean_obj_tag(v_l_183_) == 0)
{
lean_object* v_size_214_; 
v_size_214_ = lean_ctor_get(v_l_183_, 0);
lean_inc(v_size_214_);
v___y_206_ = v_size_214_;
goto v___jp_205_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___y_206_ = v___x_215_;
goto v___jp_205_;
}
v___jp_193_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_nat_add(v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec(v___y_195_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 4, v_r_16_);
lean_ctor_set(v___x_189_, 3, v_r_184_);
lean_ctor_set(v___x_189_, 2, v_v_14_);
lean_ctor_set(v___x_189_, 1, v_k_13_);
lean_ctor_set(v___x_189_, 0, v___x_197_);
v___x_199_ = v___x_189_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_r_184_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_r_16_);
v___x_199_ = v_reuseFailAlloc_203_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_201_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 4, v___x_199_);
lean_ctor_set(v___x_177_, 3, v___y_194_);
lean_ctor_set(v___x_177_, 2, v_v_182_);
lean_ctor_set(v___x_177_, 1, v_k_181_);
lean_ctor_set(v___x_177_, 0, v___x_192_);
v___x_201_ = v___x_177_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_k_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_v_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v___y_194_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
v___jp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_nat_add(v___x_204_, v___y_206_);
lean_dec(v___y_206_);
lean_dec(v___x_204_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_l_183_);
lean_ctor_set(v___x_18_, 3, v_l_166_);
lean_ctor_set(v___x_18_, 2, v_v_165_);
lean_ctor_set(v___x_18_, 1, v_k_164_);
lean_ctor_set(v___x_18_, 0, v___x_207_);
v___x_209_ = v___x_18_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_k_164_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_v_165_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_l_166_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_l_183_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; 
v___x_210_ = lean_nat_add(v___x_161_, v_size_162_);
if (lean_obj_tag(v_r_184_) == 0)
{
lean_object* v_size_211_; 
v_size_211_ = lean_ctor_get(v_r_184_, 0);
lean_inc(v_size_211_);
v___y_194_ = v___x_209_;
v___y_195_ = v___x_210_;
v___y_196_ = v_size_211_;
goto v___jp_193_;
}
else
{
lean_object* v___x_212_; 
v___x_212_ = lean_unsigned_to_nat(0u);
v___y_194_ = v___x_209_;
v___y_195_ = v___x_210_;
v___y_196_ = v___x_212_;
goto v___jp_193_;
}
}
}
}
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
lean_del_object(v___x_18_);
v___x_222_ = lean_nat_add(v___x_161_, v_size_163_);
lean_dec(v_size_163_);
v___x_223_ = lean_nat_add(v___x_222_, v_size_162_);
lean_dec(v___x_222_);
v___x_224_ = lean_nat_add(v___x_161_, v_size_162_);
v___x_225_ = lean_nat_add(v___x_224_, v_size_180_);
lean_dec(v___x_224_);
lean_inc_ref(v_r_16_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 4, v_r_16_);
lean_ctor_set(v___x_177_, 3, v_r_167_);
lean_ctor_set(v___x_177_, 2, v_v_14_);
lean_ctor_set(v___x_177_, 1, v_k_13_);
lean_ctor_set(v___x_177_, 0, v___x_225_);
v___x_227_ = v___x_177_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_240_, 3, v_r_167_);
lean_ctor_set(v_reuseFailAlloc_240_, 4, v_r_16_);
v___x_227_ = v_reuseFailAlloc_240_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_isSharedCheck_234_ = !lean_is_exclusive(v_r_16_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; lean_object* v_unused_236_; lean_object* v_unused_237_; lean_object* v_unused_238_; lean_object* v_unused_239_; 
v_unused_235_ = lean_ctor_get(v_r_16_, 4);
lean_dec(v_unused_235_);
v_unused_236_ = lean_ctor_get(v_r_16_, 3);
lean_dec(v_unused_236_);
v_unused_237_ = lean_ctor_get(v_r_16_, 2);
lean_dec(v_unused_237_);
v_unused_238_ = lean_ctor_get(v_r_16_, 1);
lean_dec(v_unused_238_);
v_unused_239_ = lean_ctor_get(v_r_16_, 0);
lean_dec(v_unused_239_);
v___x_229_ = v_r_16_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_dec(v_r_16_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 4, v___x_227_);
lean_ctor_set(v___x_229_, 3, v_l_166_);
lean_ctor_set(v___x_229_, 2, v_v_165_);
lean_ctor_set(v___x_229_, 1, v_k_164_);
lean_ctor_set(v___x_229_, 0, v___x_223_);
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_k_164_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_v_165_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_l_166_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v___x_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_247_; 
v_l_247_ = lean_ctor_get(v_impl_160_, 3);
if (lean_obj_tag(v_l_247_) == 0)
{
lean_object* v_r_248_; lean_object* v_k_249_; lean_object* v_v_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_261_; 
lean_inc_ref(v_l_247_);
v_r_248_ = lean_ctor_get(v_impl_160_, 4);
v_k_249_ = lean_ctor_get(v_impl_160_, 1);
v_v_250_ = lean_ctor_get(v_impl_160_, 2);
v_isSharedCheck_261_ = !lean_is_exclusive(v_impl_160_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_262_ = lean_ctor_get(v_impl_160_, 3);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_impl_160_, 0);
lean_dec(v_unused_263_);
v___x_252_ = v_impl_160_;
v_isShared_253_ = v_isSharedCheck_261_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_r_248_);
lean_inc(v_v_250_);
lean_inc(v_k_249_);
lean_dec(v_impl_160_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_261_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_248_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 3, v_r_248_);
lean_ctor_set(v___x_252_, 2, v_v_14_);
lean_ctor_set(v___x_252_, 1, v_k_13_);
lean_ctor_set(v___x_252_, 0, v___x_161_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_r_248_);
lean_ctor_set(v_reuseFailAlloc_260_, 4, v_r_248_);
v___x_256_ = v_reuseFailAlloc_260_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_258_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_256_);
lean_ctor_set(v___x_18_, 3, v_l_247_);
lean_ctor_set(v___x_18_, 2, v_v_250_);
lean_ctor_set(v___x_18_, 1, v_k_249_);
lean_ctor_set(v___x_18_, 0, v___x_254_);
v___x_258_ = v___x_18_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_k_249_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_v_250_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_l_247_);
lean_ctor_set(v_reuseFailAlloc_259_, 4, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_r_264_; 
v_r_264_ = lean_ctor_get(v_impl_160_, 4);
lean_inc(v_r_264_);
if (lean_obj_tag(v_r_264_) == 0)
{
lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_289_; 
lean_inc(v_l_247_);
v_k_265_ = lean_ctor_get(v_impl_160_, 1);
v_v_266_ = lean_ctor_get(v_impl_160_, 2);
v_isSharedCheck_289_ = !lean_is_exclusive(v_impl_160_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_290_ = lean_ctor_get(v_impl_160_, 4);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_impl_160_, 3);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_impl_160_, 0);
lean_dec(v_unused_292_);
v___x_268_ = v_impl_160_;
v_isShared_269_ = v_isSharedCheck_289_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_v_266_);
lean_inc(v_k_265_);
lean_dec(v_impl_160_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_289_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_285_; 
v_k_270_ = lean_ctor_get(v_r_264_, 1);
v_v_271_ = lean_ctor_get(v_r_264_, 2);
v_isSharedCheck_285_ = !lean_is_exclusive(v_r_264_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; 
v_unused_286_ = lean_ctor_get(v_r_264_, 4);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_r_264_, 3);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_r_264_, 0);
lean_dec(v_unused_288_);
v___x_273_ = v_r_264_;
v_isShared_274_ = v_isSharedCheck_285_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_v_271_);
lean_inc(v_k_270_);
lean_dec(v_r_264_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_285_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_unsigned_to_nat(3u);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 4, v_l_247_);
lean_ctor_set(v___x_273_, 3, v_l_247_);
lean_ctor_set(v___x_273_, 2, v_v_266_);
lean_ctor_set(v___x_273_, 1, v_k_265_);
lean_ctor_set(v___x_273_, 0, v___x_161_);
v___x_277_ = v___x_273_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_k_265_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_v_266_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_l_247_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_l_247_);
v___x_277_ = v_reuseFailAlloc_284_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_279_; 
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 4, v_l_247_);
lean_ctor_set(v___x_268_, 2, v_v_14_);
lean_ctor_set(v___x_268_, 1, v_k_13_);
lean_ctor_set(v___x_268_, 0, v___x_161_);
v___x_279_ = v___x_268_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_283_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_283_, 3, v_l_247_);
lean_ctor_set(v_reuseFailAlloc_283_, 4, v_l_247_);
v___x_279_ = v_reuseFailAlloc_283_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v___x_279_);
lean_ctor_set(v___x_18_, 3, v___x_277_);
lean_ctor_set(v___x_18_, 2, v_v_271_);
lean_ctor_set(v___x_18_, 1, v_k_270_);
lean_ctor_set(v___x_18_, 0, v___x_275_);
v___x_281_ = v___x_18_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_k_270_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v_v_271_);
lean_ctor_set(v_reuseFailAlloc_282_, 3, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_282_, 4, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_unsigned_to_nat(2u);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 4, v_r_264_);
lean_ctor_set(v___x_18_, 3, v_impl_160_);
lean_ctor_set(v___x_18_, 0, v___x_293_);
v___x_295_ = v___x_18_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_k_13_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_v_14_);
lean_ctor_set(v_reuseFailAlloc_296_, 3, v_impl_160_);
lean_ctor_set(v_reuseFailAlloc_296_, 4, v_r_264_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(1u);
v___x_299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_k_9_);
lean_ctor_set(v___x_299_, 2, v_v_10_);
lean_ctor_set(v___x_299_, 3, v_t_11_);
lean_ctor_set(v___x_299_, 4, v_t_11_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v_ks_304_; lean_object* v_vs_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_329_; 
v_ks_304_ = lean_ctor_get(v_x_300_, 0);
v_vs_305_ = lean_ctor_get(v_x_300_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_329_ == 0)
{
v___x_307_ = v_x_300_;
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_vs_305_);
lean_inc(v_ks_304_);
lean_dec(v_x_300_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_ks_304_);
v___x_310_ = lean_nat_dec_lt(v_x_301_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec(v_x_301_);
v___x_311_ = lean_array_push(v_ks_304_, v_x_302_);
v___x_312_ = lean_array_push(v_vs_305_, v_x_303_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_312_);
lean_ctor_set(v___x_307_, 0, v___x_311_);
v___x_314_ = v___x_307_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v_k_x27_316_; uint8_t v___x_317_; 
v_k_x27_316_ = lean_array_fget_borrowed(v_ks_304_, v_x_301_);
v___x_317_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_302_, v_k_x27_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_319_; 
if (v_isShared_308_ == 0)
{
v___x_319_ = v___x_307_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_ks_304_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_vs_305_);
v___x_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_x_301_, v___x_320_);
lean_dec(v_x_301_);
v_x_300_ = v___x_319_;
v_x_301_ = v___x_321_;
goto _start;
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_array_fset(v_ks_304_, v_x_301_, v_x_302_);
v___x_325_ = lean_array_fset(v_vs_305_, v_x_301_, v_x_303_);
lean_dec(v_x_301_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_325_);
lean_ctor_set(v___x_307_, 0, v___x_324_);
v___x_327_ = v___x_307_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2___redArg(lean_object* v_n_330_, lean_object* v_k_331_, lean_object* v_v_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3___redArg(v_n_330_, v___x_333_, v_k_331_, v_v_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(lean_object* v_x_336_, size_t v_x_337_, size_t v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v_es_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v_j_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_es_341_ = lean_ctor_get(v_x_336_, 0);
v___x_342_ = ((size_t)31ULL);
v___x_343_ = lean_usize_land(v_x_337_, v___x_342_);
v_j_344_ = lean_usize_to_nat(v___x_343_);
v___x_345_ = lean_array_get_size(v_es_341_);
v___x_346_ = lean_nat_dec_lt(v_j_344_, v___x_345_);
if (v___x_346_ == 0)
{
lean_dec(v_j_344_);
lean_dec(v_x_340_);
lean_dec_ref(v_x_339_);
return v_x_336_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_385_; 
lean_inc_ref(v_es_341_);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v_x_336_, 0);
lean_dec(v_unused_386_);
v___x_348_ = v_x_336_;
v_isShared_349_ = v_isSharedCheck_385_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_x_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_385_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_v_350_; lean_object* v___x_351_; lean_object* v_xs_x27_352_; lean_object* v___y_354_; 
v_v_350_ = lean_array_fget(v_es_341_, v_j_344_);
v___x_351_ = lean_box(0);
v_xs_x27_352_ = lean_array_fset(v_es_341_, v_j_344_, v___x_351_);
switch(lean_obj_tag(v_v_350_))
{
case 0:
{
lean_object* v_key_359_; lean_object* v_val_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_370_; 
v_key_359_ = lean_ctor_get(v_v_350_, 0);
v_val_360_ = lean_ctor_get(v_v_350_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_v_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_362_ = v_v_350_;
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_val_360_);
lean_inc(v_key_359_);
lean_dec(v_v_350_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_370_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
uint8_t v___x_364_; 
v___x_364_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_339_, v_key_359_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_del_object(v___x_362_);
v___x_365_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_359_, v_val_360_, v_x_339_, v_x_340_);
v___x_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___y_354_ = v___x_366_;
goto v___jp_353_;
}
else
{
lean_object* v___x_368_; 
lean_dec(v_val_360_);
lean_dec(v_key_359_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 1, v_x_340_);
lean_ctor_set(v___x_362_, 0, v_x_339_);
v___x_368_ = v___x_362_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_x_339_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_x_340_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
v___y_354_ = v___x_368_;
goto v___jp_353_;
}
}
}
}
case 1:
{
lean_object* v_node_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_383_; 
v_node_371_ = lean_ctor_get(v_v_350_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v_v_350_);
if (v_isSharedCheck_383_ == 0)
{
v___x_373_ = v_v_350_;
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_node_371_);
lean_dec(v_v_350_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_usize_shift_right(v_x_337_, v___x_375_);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_x_338_, v___x_377_);
v___x_379_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(v_node_371_, v___x_376_, v___x_378_, v_x_339_, v_x_340_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v___y_354_ = v___x_381_;
goto v___jp_353_;
}
}
}
default: 
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_x_339_);
lean_ctor_set(v___x_384_, 1, v_x_340_);
v___y_354_ = v___x_384_;
goto v___jp_353_;
}
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_array_fset(v_xs_x27_352_, v_j_344_, v___y_354_);
lean_dec(v_j_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_355_);
v___x_357_ = v___x_348_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_object* v_ks_387_; lean_object* v_vs_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_406_; 
v_ks_387_ = lean_ctor_get(v_x_336_, 0);
v_vs_388_ = lean_ctor_get(v_x_336_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_336_);
if (v_isSharedCheck_406_ == 0)
{
v___x_390_ = v_x_336_;
v_isShared_391_ = v_isSharedCheck_406_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_vs_388_);
lean_inc(v_ks_387_);
lean_dec(v_x_336_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_406_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_ks_387_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_vs_388_);
v___x_393_ = v_reuseFailAlloc_405_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v_newNode_394_; size_t v___x_395_; uint8_t v___x_396_; 
v_newNode_394_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2___redArg(v___x_393_, v_x_339_, v_x_340_);
v___x_395_ = ((size_t)7ULL);
v___x_396_ = lean_usize_dec_le(v___x_395_, v_x_338_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_394_);
v___x_398_ = lean_unsigned_to_nat(4u);
v___x_399_ = lean_nat_dec_lt(v___x_397_, v___x_398_);
lean_dec(v___x_397_);
if (v___x_399_ == 0)
{
lean_object* v_ks_400_; lean_object* v_vs_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_ks_400_ = lean_ctor_get(v_newNode_394_, 0);
lean_inc_ref(v_ks_400_);
v_vs_401_ = lean_ctor_get(v_newNode_394_, 1);
lean_inc_ref(v_vs_401_);
lean_dec_ref(v_newNode_394_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___closed__0);
v___x_404_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg(v_x_338_, v_ks_400_, v_vs_401_, v___x_402_, v___x_403_);
lean_dec_ref(v_vs_401_);
lean_dec_ref(v_ks_400_);
return v___x_404_;
}
else
{
return v_newNode_394_;
}
}
else
{
return v_newNode_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg(size_t v_depth_407_, lean_object* v_keys_408_, lean_object* v_vals_409_, lean_object* v_i_410_, lean_object* v_entries_411_){
_start:
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = lean_array_get_size(v_keys_408_);
v___x_413_ = lean_nat_dec_lt(v_i_410_, v___x_412_);
if (v___x_413_ == 0)
{
lean_dec(v_i_410_);
return v_entries_411_;
}
else
{
lean_object* v_k_414_; lean_object* v_v_415_; uint64_t v___x_416_; size_t v_h_417_; size_t v___x_418_; lean_object* v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v_h_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v_k_414_ = lean_array_fget_borrowed(v_keys_408_, v_i_410_);
v_v_415_ = lean_array_fget_borrowed(v_vals_409_, v_i_410_);
v___x_416_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_414_);
v_h_417_ = lean_uint64_to_usize(v___x_416_);
v___x_418_ = ((size_t)5ULL);
v___x_419_ = lean_unsigned_to_nat(1u);
v___x_420_ = ((size_t)1ULL);
v___x_421_ = lean_usize_sub(v_depth_407_, v___x_420_);
v___x_422_ = lean_usize_mul(v___x_418_, v___x_421_);
v_h_423_ = lean_usize_shift_right(v_h_417_, v___x_422_);
v___x_424_ = lean_nat_add(v_i_410_, v___x_419_);
lean_dec(v_i_410_);
lean_inc(v_v_415_);
lean_inc(v_k_414_);
v___x_425_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(v_entries_411_, v_h_423_, v_depth_407_, v_k_414_, v_v_415_);
v_i_410_ = v___x_424_;
v_entries_411_ = v___x_425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_427_, lean_object* v_keys_428_, lean_object* v_vals_429_, lean_object* v_i_430_, lean_object* v_entries_431_){
_start:
{
size_t v_depth_boxed_432_; lean_object* v_res_433_; 
v_depth_boxed_432_ = lean_unbox_usize(v_depth_427_);
lean_dec(v_depth_427_);
v_res_433_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg(v_depth_boxed_432_, v_keys_428_, v_vals_429_, v_i_430_, v_entries_431_);
lean_dec_ref(v_vals_429_);
lean_dec_ref(v_keys_428_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg___boxed(lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
size_t v_x_1931__boxed_439_; size_t v_x_1932__boxed_440_; lean_object* v_res_441_; 
v_x_1931__boxed_439_ = lean_unbox_usize(v_x_435_);
lean_dec(v_x_435_);
v_x_1932__boxed_440_ = lean_unbox_usize(v_x_436_);
lean_dec(v_x_436_);
v_res_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(v_x_434_, v_x_1931__boxed_439_, v_x_1932__boxed_440_, v_x_437_, v_x_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1___redArg(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
uint64_t v___x_445_; size_t v___x_446_; size_t v___x_447_; lean_object* v___x_448_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_443_);
v___x_446_ = lean_uint64_to_usize(v___x_445_);
v___x_447_ = ((size_t)1ULL);
v___x_448_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(v_x_442_, v___x_446_, v___x_447_, v_x_443_, v_x_444_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(lean_object* v_s_449_, lean_object* v_i_450_, lean_object* v_b_451_){
_start:
{
lean_object* v_ordered_452_; lean_object* v_index_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_463_; 
v_ordered_452_ = lean_ctor_get(v_s_449_, 0);
v_index_453_ = lean_ctor_get(v_s_449_, 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_s_449_);
if (v_isSharedCheck_463_ == 0)
{
v___x_455_ = v_s_449_;
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_index_453_);
lean_inc(v_ordered_452_);
lean_dec(v_s_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_463_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v_lin_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v_lin_457_ = lean_ctor_get(v_b_451_, 0);
lean_inc_ref(v_lin_457_);
lean_inc(v_i_450_);
v___x_458_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(v_i_450_, v_b_451_, v_ordered_452_);
v___x_459_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1___redArg(v_index_453_, v_lin_457_, v_i_450_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_459_);
lean_ctor_set(v___x_455_, 0, v___x_458_);
v___x_461_ = v___x_455_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_k_465_, lean_object* v_v_466_, lean_object* v_t_467_, lean_object* v_hl_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__0___redArg(v_k_465_, v_v_466_, v_t_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1___redArg(v_x_471_, v_x_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1(lean_object* v_00_u03b2_475_, lean_object* v_x_476_, size_t v_x_477_, size_t v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___redArg(v_x_476_, v_x_477_, v_x_478_, v_x_479_, v_x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1___boxed(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
size_t v_x_2125__boxed_488_; size_t v_x_2126__boxed_489_; lean_object* v_res_490_; 
v_x_2125__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_x_2126__boxed_489_ = lean_unbox_usize(v_x_485_);
lean_dec(v_x_485_);
v_res_490_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1(v_00_u03b2_482_, v_x_483_, v_x_2125__boxed_488_, v_x_2126__boxed_489_, v_x_486_, v_x_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_491_, lean_object* v_n_492_, lean_object* v_k_493_, lean_object* v_v_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2___redArg(v_n_492_, v_k_493_, v_v_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_496_, size_t v_depth_497_, lean_object* v_keys_498_, lean_object* v_vals_499_, lean_object* v_heq_500_, lean_object* v_i_501_, lean_object* v_entries_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___redArg(v_depth_497_, v_keys_498_, v_vals_499_, v_i_501_, v_entries_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_504_, lean_object* v_depth_505_, lean_object* v_keys_506_, lean_object* v_vals_507_, lean_object* v_heq_508_, lean_object* v_i_509_, lean_object* v_entries_510_){
_start:
{
size_t v_depth_boxed_511_; lean_object* v_res_512_; 
v_depth_boxed_511_ = lean_unbox_usize(v_depth_505_);
lean_dec(v_depth_505_);
v_res_512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__3(v_00_u03b2_504_, v_depth_boxed_511_, v_keys_506_, v_vals_507_, v_heq_508_, v_i_509_, v_entries_510_);
lean_dec_ref(v_vals_507_);
lean_dec_ref(v_keys_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt_spec__1_spec__1_spec__2_spec__3___redArg(v_x_514_, v_x_515_, v_x_516_, v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg(lean_object* v_t_519_, lean_object* v_k_520_){
_start:
{
if (lean_obj_tag(v_t_519_) == 0)
{
lean_object* v_k_521_; lean_object* v_v_522_; lean_object* v_l_523_; lean_object* v_r_524_; uint8_t v___x_525_; 
v_k_521_ = lean_ctor_get(v_t_519_, 1);
v_v_522_ = lean_ctor_get(v_t_519_, 2);
v_l_523_ = lean_ctor_get(v_t_519_, 3);
v_r_524_ = lean_ctor_get(v_t_519_, 4);
v___x_525_ = lean_int_dec_lt(v_k_520_, v_k_521_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
v___x_526_ = lean_int_dec_eq(v_k_520_, v_k_521_);
if (v___x_526_ == 0)
{
v_t_519_ = v_r_524_;
goto _start;
}
else
{
lean_object* v___x_528_; 
lean_inc(v_v_522_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v_v_522_);
return v___x_528_;
}
}
else
{
v_t_519_ = v_l_523_;
goto _start;
}
}
else
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg___boxed(lean_object* v_t_531_, lean_object* v_k_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg(v_t_531_, v_k_532_);
lean_dec(v_k_532_);
lean_dec(v_t_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_534_, lean_object* v_vals_535_, lean_object* v_i_536_, lean_object* v_k_537_){
_start:
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_get_size(v_keys_534_);
v___x_539_ = lean_nat_dec_lt(v_i_536_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec(v_i_536_);
v___x_540_ = lean_box(0);
return v___x_540_;
}
else
{
lean_object* v_k_x27_541_; uint8_t v___x_542_; 
v_k_x27_541_ = lean_array_fget_borrowed(v_keys_534_, v_i_536_);
v___x_542_ = l_Int_Internal_Linear_instBEqPoly_beq(v_k_537_, v_k_x27_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(1u);
v___x_544_ = lean_nat_add(v_i_536_, v___x_543_);
lean_dec(v_i_536_);
v_i_536_ = v___x_544_;
goto _start;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_array_fget_borrowed(v_vals_535_, v_i_536_);
lean_dec(v_i_536_);
lean_inc(v___x_546_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_548_, lean_object* v_vals_549_, lean_object* v_i_550_, lean_object* v_k_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_548_, v_vals_549_, v_i_550_, v_k_551_);
lean_dec_ref(v_k_551_);
lean_dec_ref(v_vals_549_);
lean_dec_ref(v_keys_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_553_, size_t v_x_554_, lean_object* v_x_555_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v_es_556_; lean_object* v___x_557_; size_t v___x_558_; size_t v___x_559_; lean_object* v_j_560_; lean_object* v___x_561_; 
v_es_556_ = lean_ctor_get(v_x_553_, 0);
v___x_557_ = lean_box(2);
v___x_558_ = ((size_t)31ULL);
v___x_559_ = lean_usize_land(v_x_554_, v___x_558_);
v_j_560_ = lean_usize_to_nat(v___x_559_);
v___x_561_ = lean_array_get_borrowed(v___x_557_, v_es_556_, v_j_560_);
lean_dec(v_j_560_);
switch(lean_obj_tag(v___x_561_))
{
case 0:
{
lean_object* v_key_562_; lean_object* v_val_563_; uint8_t v___x_564_; 
v_key_562_ = lean_ctor_get(v___x_561_, 0);
v_val_563_ = lean_ctor_get(v___x_561_, 1);
v___x_564_ = l_Int_Internal_Linear_instBEqPoly_beq(v_x_555_, v_key_562_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
v___x_565_ = lean_box(0);
return v___x_565_;
}
else
{
lean_object* v___x_566_; 
lean_inc(v_val_563_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v_val_563_);
return v___x_566_;
}
}
case 1:
{
lean_object* v_node_567_; size_t v___x_568_; size_t v___x_569_; 
v_node_567_ = lean_ctor_get(v___x_561_, 0);
v___x_568_ = ((size_t)5ULL);
v___x_569_ = lean_usize_shift_right(v_x_554_, v___x_568_);
v_x_553_ = v_node_567_;
v_x_554_ = v___x_569_;
goto _start;
}
default: 
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
}
}
else
{
lean_object* v_ks_572_; lean_object* v_vs_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_ks_572_ = lean_ctor_get(v_x_553_, 0);
v_vs_573_ = lean_ctor_get(v_x_553_, 1);
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_572_, v_vs_573_, v___x_574_, v_x_555_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
size_t v_x_391__boxed_579_; lean_object* v_res_580_; 
v_x_391__boxed_579_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_res_580_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg(v_x_576_, v_x_391__boxed_579_, v_x_578_);
lean_dec_ref(v_x_578_);
lean_dec_ref(v_x_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
uint64_t v___x_583_; size_t v___x_584_; lean_object* v___x_585_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_582_);
v___x_584_ = lean_uint64_to_usize(v___x_583_);
v___x_585_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg(v_x_581_, v___x_584_, v_x_582_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg___boxed(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(v_x_586_, v_x_587_);
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(lean_object* v_s_589_, lean_object* v_lin_590_){
_start:
{
lean_object* v_ordered_591_; lean_object* v_index_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_612_; 
v_ordered_591_ = lean_ctor_get(v_s_589_, 0);
v_index_592_ = lean_ctor_get(v_s_589_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_s_589_);
if (v_isSharedCheck_612_ == 0)
{
v___x_594_ = v_s_589_;
v_isShared_595_ = v_isSharedCheck_612_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_index_592_);
lean_inc(v_ordered_591_);
lean_dec(v_s_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_612_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(v_index_592_, v_lin_590_);
lean_dec_ref(v_index_592_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; 
lean_del_object(v___x_594_);
lean_dec(v_ordered_591_);
v___x_597_ = lean_box(0);
return v___x_597_;
}
else
{
lean_object* v_val_598_; lean_object* v___x_599_; 
v_val_598_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_val_598_);
lean_dec_ref_known(v___x_596_, 1);
v___x_599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg(v_ordered_591_, v_val_598_);
lean_dec(v_ordered_591_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; 
lean_dec(v_val_598_);
lean_del_object(v___x_594_);
v___x_600_ = lean_box(0);
return v___x_600_;
}
else
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_val_601_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v___x_599_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v___x_599_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v_val_601_);
lean_ctor_set(v___x_594_, 0, v_val_598_);
v___x_606_ = v___x_594_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_598_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_val_601_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_606_);
v___x_608_ = v___x_603_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f___boxed(lean_object* v_s_613_, lean_object* v_lin_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(v_s_613_, v_lin_614_);
lean_dec_ref(v_lin_614_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(v_x_617_, v_x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0(v_00_u03b2_620_, v_x_621_, v_x_622_);
lean_dec_ref(v_x_622_);
lean_dec_ref(v_x_621_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1(lean_object* v_00_u03b4_624_, lean_object* v_t_625_, lean_object* v_k_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___redArg(v_t_625_, v_k_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1___boxed(lean_object* v_00_u03b4_628_, lean_object* v_t_629_, lean_object* v_k_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__1(v_00_u03b4_628_, v_t_629_, v_k_630_);
lean_dec(v_k_630_);
lean_dec(v_t_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_632_, lean_object* v_x_633_, size_t v_x_634_, lean_object* v_x_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___redArg(v_x_633_, v_x_634_, v_x_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_500__boxed_641_; lean_object* v_res_642_; 
v_x_500__boxed_641_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_642_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0(v_00_u03b2_637_, v_x_638_, v_x_500__boxed_641_, v_x_640_);
lean_dec_ref(v_x_640_);
lean_dec_ref(v_x_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_643_, lean_object* v_keys_644_, lean_object* v_vals_645_, lean_object* v_heq_646_, lean_object* v_i_647_, lean_object* v_k_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_644_, v_vals_645_, v_i_647_, v_k_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_650_, lean_object* v_keys_651_, lean_object* v_vals_652_, lean_object* v_heq_653_, lean_object* v_i_654_, lean_object* v_k_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_650_, v_keys_651_, v_vals_652_, v_heq_653_, v_i_654_, v_k_655_);
lean_dec_ref(v_k_655_);
lean_dec_ref(v_vals_652_);
lean_dec_ref(v_keys_651_);
return v_res_656_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(lean_object* v_00_u03b1_663_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_665_ = l_Lean_Expr_isConstOf(v_00_u03b1_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__3));
v___x_667_ = l_Lean_Expr_isConstOf(v_00_u03b1_663_, v___x_666_);
return v___x_667_;
}
else
{
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___boxed(lean_object* v_00_u03b1_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_00_u03b1_668_);
lean_dec_ref(v_00_u03b1_668_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(lean_object* v_e_679_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = l_Lean_Expr_cleanupAnnotations(v_e_679_);
v___x_681_ = l_Lean_Expr_isApp(v___x_680_);
if (v___x_681_ == 0)
{
lean_dec_ref(v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; uint8_t v___x_683_; 
v___x_682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_680_);
lean_dec_ref(v___x_680_);
v___x_683_ = l_Lean_Expr_isApp(v___x_682_);
if (v___x_683_ == 0)
{
lean_dec_ref(v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_682_);
lean_dec_ref(v___x_682_);
v___x_685_ = l_Lean_Expr_isApp(v___x_684_);
if (v___x_685_ == 0)
{
lean_dec_ref(v___x_684_);
return v___x_685_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_684_);
v___x_687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1));
v___x_688_ = l_Lean_Expr_isConstOf(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
lean_dec_ref(v___x_684_);
v___x_689_ = l_Lean_Expr_isApp(v___x_686_);
if (v___x_689_ == 0)
{
lean_dec_ref(v___x_686_);
return v___x_689_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_Expr_appFnCleanup___redArg(v___x_686_);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4));
v___x_692_ = l_Lean_Expr_isConstOf(v___x_690_, v___x_691_);
lean_dec_ref(v___x_690_);
if (v___x_692_ == 0)
{
lean_dec_ref(v___x_686_);
return v___x_692_;
}
else
{
lean_object* v_arg_693_; uint8_t v___x_694_; 
v_arg_693_ = lean_ctor_get(v___x_686_, 1);
lean_inc_ref(v_arg_693_);
lean_dec_ref(v___x_686_);
v___x_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_693_);
lean_dec_ref(v_arg_693_);
return v___x_694_;
}
}
}
else
{
lean_object* v_arg_695_; uint8_t v___x_696_; 
lean_dec_ref(v___x_686_);
v_arg_695_ = lean_ctor_get(v___x_684_, 1);
lean_inc_ref(v_arg_695_);
lean_dec_ref(v___x_684_);
v___x_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_695_);
lean_dec_ref(v_arg_695_);
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___boxed(lean_object* v_e_697_){
_start:
{
uint8_t v_res_698_; lean_object* v_r_699_; 
v_res_698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom(v_e_697_);
lean_dec_ref(v_e_697_);
v_r_699_ = lean_box(v_res_698_);
return v_r_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(lean_object* v_e_700_, lean_object* v_a_701_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_700_, v_a_701_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_780_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_780_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_780_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_780_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = l_Lean_Expr_cleanupAnnotations(v_a_707_);
lean_dec(v_a_707_);
v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_711_);
lean_del_object(v___x_709_);
goto v___jp_703_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
v___x_714_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_714_ == 0)
{
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_del_object(v___x_709_);
goto v___jp_703_;
}
else
{
lean_object* v___x_715_; uint8_t v___x_716_; 
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
v___x_716_ = l_Lean_Expr_isApp(v___x_715_);
if (v___x_716_ == 0)
{
lean_dec_ref(v___x_715_);
lean_dec_ref(v___x_713_);
lean_dec_ref(v___x_711_);
lean_del_object(v___x_709_);
goto v___jp_703_;
}
else
{
lean_object* v_arg_717_; lean_object* v_arg_718_; lean_object* v_arg_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_arg_717_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_arg_717_);
lean_dec_ref(v___x_711_);
v_arg_718_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_arg_718_);
lean_dec_ref(v___x_713_);
v_arg_719_ = lean_ctor_get(v___x_715_, 1);
lean_inc_ref(v_arg_719_);
v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_715_);
lean_dec_ref(v___x_715_);
v___x_721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__1));
v___x_722_ = l_Lean_Expr_isConstOf(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
uint8_t v___x_723_; 
v___x_723_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_723_ == 0)
{
lean_dec_ref(v___x_720_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
lean_del_object(v___x_709_);
goto v___jp_703_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isArithAtom___closed__4));
v___x_726_ = l_Lean_Expr_isConstOf(v___x_724_, v___x_725_);
lean_dec_ref(v___x_724_);
if (v___x_726_ == 0)
{
lean_dec_ref(v___x_720_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
lean_del_object(v___x_709_);
goto v___jp_703_;
}
else
{
lean_object* v_arg_727_; uint8_t v___x_728_; 
v_arg_727_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_arg_727_);
lean_dec_ref(v___x_720_);
v___x_728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_dec_ref(v_arg_727_);
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
v___x_729_ = lean_box(0);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_729_);
v___x_731_ = v___x_709_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; uint8_t v_____do__lift_736_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_734_ = l_Lean_Expr_isConstOf(v_arg_727_, v___x_733_);
lean_dec_ref(v_arg_727_);
if (v___x_734_ == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_719_, v_a_701_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; uint8_t v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
v_____do__lift_736_ = v___x_748_;
goto v___jp_735_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
lean_del_object(v___x_709_);
v_a_749_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_746_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_arg_719_, v_a_701_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; uint8_t v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_757_, 1);
v___x_759_ = lean_unbox(v_a_758_);
lean_dec(v_a_758_);
v_____do__lift_736_ = v___x_759_;
goto v___jp_735_;
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
lean_del_object(v___x_709_);
v_a_760_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_757_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_757_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
v___jp_735_:
{
if (v_____do__lift_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_739_; 
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
v___x_737_ = lean_box(0);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_737_);
v___x_739_ = v___x_709_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_741_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_741_, 0, v_arg_718_);
lean_ctor_set(v___x_741_, 1, v_arg_717_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*2, v___x_722_);
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*2 + 1, v___x_734_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_742_);
v___x_744_ = v___x_709_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_768_; 
lean_dec_ref(v___x_720_);
v___x_768_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt(v_arg_719_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec_ref(v_arg_719_);
lean_dec_ref(v_arg_718_);
lean_dec_ref(v_arg_717_);
v___x_769_ = lean_box(0);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_769_);
v___x_771_ = v___x_709_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v___x_773_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_isNatOrInt___closed__1));
v___x_774_ = l_Lean_Expr_isConstOf(v_arg_719_, v___x_773_);
lean_dec_ref(v_arg_719_);
v___x_775_ = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(v___x_775_, 0, v_arg_718_);
lean_ctor_set(v___x_775_, 1, v_arg_717_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2, v___x_722_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*2 + 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_776_);
v___x_778_ = v___x_709_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
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
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_706_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_706_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
v___jp_703_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg___boxed(lean_object* v_e_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(v_e_789_, v_a_790_);
lean_dec(v_a_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f(lean_object* v_e_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(v_e_793_, v_a_795_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___boxed(lean_object* v_e_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f(v_e_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry_spec__0(lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = lean_nat_to_int(v_a_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(lean_object* v_p_809_, lean_object* v_atom_810_, lean_object* v_entries_811_){
_start:
{
lean_object* v_k_812_; lean_object* v___x_813_; lean_object* v_lin_814_; lean_object* v___y_816_; 
v_k_812_ = l_Int_Internal_Linear_Poly_getConst(v_p_809_);
v___x_813_ = lean_int_neg(v_k_812_);
v_lin_814_ = l_Int_Internal_Linear_Poly_addConst(v_p_809_, v___x_813_);
lean_dec(v___x_813_);
if (lean_obj_tag(v_lin_814_) == 0)
{
lean_dec_ref_known(v_lin_814_, 1);
lean_dec(v_k_812_);
lean_dec_ref(v_atom_810_);
return v_entries_811_;
}
else
{
lean_object* v_ordered_820_; 
v_ordered_820_ = lean_ctor_get(v_entries_811_, 0);
if (lean_obj_tag(v_ordered_820_) == 0)
{
lean_object* v_size_821_; 
v_size_821_ = lean_ctor_get(v_ordered_820_, 0);
lean_inc(v_size_821_);
v___y_816_ = v_size_821_;
goto v___jp_815_;
}
else
{
lean_object* v___x_822_; 
v___x_822_ = lean_unsigned_to_nat(0u);
v___y_816_ = v___x_822_;
goto v___jp_815_;
}
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_nat_to_int(v___y_816_);
v___x_818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_818_, 0, v_lin_814_);
lean_ctor_set(v___x_818_, 1, v_k_812_);
lean_ctor_set(v___x_818_, 2, v_atom_810_);
v___x_819_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v_entries_811_, v___x_817_, v___x_818_);
return v___x_819_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_to_int(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0);
v___x_826_ = lean_int_neg(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries(lean_object* v_gen_838_, lean_object* v_c_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(v_c_839_, v_a_847_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_963_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_963_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_963_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_963_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
if (lean_obj_tag(v_a_852_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_854_);
v_val_856_ = lean_ctor_get(v_a_852_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_958_ == 0)
{
v___x_858_ = v_a_852_;
v_isShared_859_ = v_isSharedCheck_958_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v_a_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_958_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_a_860_; lean_object* v_b_861_; uint8_t v_isEq_862_; uint8_t v_isNat_863_; lean_object* v_fst_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; 
v_a_860_ = lean_ctor_get(v_val_856_, 0);
lean_inc_ref(v_a_860_);
v_b_861_ = lean_ctor_get(v_val_856_, 1);
lean_inc_ref(v_b_861_);
v_isEq_862_ = lean_ctor_get_uint8(v_val_856_, sizeof(void*)*2);
v_isNat_863_ = lean_ctor_get_uint8(v_val_856_, sizeof(void*)*2 + 1);
lean_dec(v_val_856_);
if (v_isNat_863_ == 0)
{
lean_object* v___x_923_; 
lean_del_object(v___x_858_);
v___x_923_ = lean_box(0);
v_fst_865_ = v_a_860_;
v_fst_866_ = v_b_861_;
v_snd_867_ = v___x_923_;
v___y_868_ = v_a_840_;
v___y_869_ = v_a_841_;
v___y_870_ = v_a_842_;
v___y_871_ = v_a_843_;
v___y_872_ = v_a_844_;
v___y_873_ = v_a_845_;
v___y_874_ = v_a_846_;
v___y_875_ = v_a_847_;
v___y_876_ = v_a_848_;
v___y_877_ = v_a_849_;
goto v___jp_864_;
}
else
{
lean_object* v___x_924_; 
lean_inc_ref(v_a_860_);
v___x_924_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_a_860_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___x_928_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
v_fst_926_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_fst_926_);
v_snd_927_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_snd_927_);
lean_dec(v_a_925_);
lean_inc_ref(v_b_861_);
v___x_928_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_b_861_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___y_933_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v_fst_930_ = lean_ctor_get(v_a_929_, 0);
lean_inc(v_fst_930_);
v_snd_931_ = lean_ctor_get(v_a_929_, 1);
lean_inc(v_snd_931_);
lean_dec(v_a_929_);
if (v_isEq_862_ == 0)
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__4));
v___y_933_ = v___x_940_;
goto v___jp_932_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__6));
v___y_933_ = v___x_941_;
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_934_ = lean_box(0);
lean_inc(v___y_933_);
v___x_935_ = l_Lean_mkConst(v___y_933_, v___x_934_);
lean_inc(v_fst_930_);
lean_inc(v_fst_926_);
v___x_936_ = l_Lean_mkApp6(v___x_935_, v_a_860_, v_b_861_, v_fst_926_, v_fst_930_, v_snd_927_, v_snd_931_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_936_);
v___x_938_ = v___x_858_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
v_fst_865_ = v_fst_926_;
v_fst_866_ = v_fst_930_;
v_snd_867_ = v___x_938_;
v___y_868_ = v_a_840_;
v___y_869_ = v_a_841_;
v___y_870_ = v_a_842_;
v___y_871_ = v_a_843_;
v___y_872_ = v_a_844_;
v___y_873_ = v_a_845_;
v___y_874_ = v_a_846_;
v___y_875_ = v_a_847_;
v___y_876_ = v_a_848_;
v___y_877_ = v_a_849_;
goto v___jp_864_;
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_snd_927_);
lean_dec(v_fst_926_);
lean_dec_ref(v_b_861_);
lean_dec_ref(v_a_860_);
lean_del_object(v___x_858_);
lean_dec(v_gen_838_);
v_a_942_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_928_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_928_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v_b_861_);
lean_dec_ref(v_a_860_);
lean_del_object(v___x_858_);
lean_dec(v_gen_838_);
v_a_950_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_924_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_924_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
v___jp_864_:
{
lean_object* v___x_878_; 
lean_inc(v_gen_838_);
v___x_878_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_865_, v_gen_838_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; lean_object* v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_866_, v_gen_838_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_906_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_906_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_906_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_inc(v_a_881_);
lean_inc(v_a_879_);
v___x_885_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_885_, 0, v_a_879_);
lean_ctor_set(v___x_885_, 1, v_a_881_);
v___x_886_ = l_Int_Internal_Linear_Expr_norm(v___x_885_);
lean_dec_ref_known(v___x_885_, 2);
if (v_isEq_862_ == 0)
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_887_ = 0;
v___x_888_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_888_, 0, v_snd_867_);
lean_ctor_set(v___x_888_, 1, v_a_879_);
lean_ctor_set(v___x_888_, 2, v_a_881_);
lean_ctor_set_uint8(v___x_888_, sizeof(void*)*3, v___x_887_);
v___x_889_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
v___x_890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_886_, v___x_888_, v___x_889_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_890_);
v___x_892_ = v___x_883_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1);
lean_inc_ref(v___x_886_);
v___x_895_ = l_Int_Internal_Linear_Poly_mul(v___x_886_, v___x_894_);
v___x_896_ = 2;
lean_inc(v_a_881_);
lean_inc(v_a_879_);
lean_inc(v_snd_867_);
v___x_897_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_897_, 0, v_snd_867_);
lean_ctor_set(v___x_897_, 1, v_a_879_);
lean_ctor_set(v___x_897_, 2, v_a_881_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*3, v___x_896_);
v___x_898_ = 1;
v___x_899_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_899_, 0, v_snd_867_);
lean_ctor_set(v___x_899_, 1, v_a_879_);
lean_ctor_set(v___x_899_, 2, v_a_881_);
lean_ctor_set_uint8(v___x_899_, sizeof(void*)*3, v___x_898_);
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_886_, v___x_899_, v___x_900_);
v___x_902_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_mkEntry(v___x_895_, v___x_897_, v___x_901_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_902_);
v___x_904_ = v___x_883_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_a_879_);
lean_dec(v_snd_867_);
v_a_907_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_880_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_880_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_snd_867_);
lean_dec_ref(v_fst_866_);
lean_dec(v_gen_838_);
v_a_915_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_878_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_878_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v_a_852_);
lean_dec(v_gen_838_);
v___x_959_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_959_);
v___x_961_ = v___x_854_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_gen_838_);
v_a_964_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_851_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_851_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___boxed(lean_object* v_gen_972_, lean_object* v_c_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries(v_gen_972_, v_c_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__1(lean_object* v_b_986_, lean_object* v_k_987_, lean_object* v_t_988_){
_start:
{
if (lean_obj_tag(v_t_988_) == 0)
{
lean_object* v_size_989_; lean_object* v_k_990_; lean_object* v_v_991_; lean_object* v_l_992_; lean_object* v_r_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1016_; 
v_size_989_ = lean_ctor_get(v_t_988_, 0);
v_k_990_ = lean_ctor_get(v_t_988_, 1);
v_v_991_ = lean_ctor_get(v_t_988_, 2);
v_l_992_ = lean_ctor_get(v_t_988_, 3);
v_r_993_ = lean_ctor_get(v_t_988_, 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_t_988_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_995_ = v_t_988_;
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_r_993_);
lean_inc(v_l_992_);
lean_inc(v_v_991_);
lean_inc(v_k_990_);
lean_inc(v_size_989_);
lean_dec(v_t_988_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1016_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
uint8_t v___x_997_; 
v___x_997_ = lean_int_dec_lt(v_k_987_, v_k_990_);
if (v___x_997_ == 0)
{
uint8_t v___x_998_; 
v___x_998_ = lean_int_dec_eq(v_k_987_, v_k_990_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__1(v_b_986_, v_k_987_, v_r_993_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 4, v___x_999_);
v___x_1001_ = v___x_995_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_size_989_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v_k_1003_; lean_object* v_k_1004_; uint8_t v___x_1005_; 
lean_dec(v_k_990_);
v_k_1003_ = lean_ctor_get(v_v_991_, 1);
v_k_1004_ = lean_ctor_get(v_b_986_, 1);
v___x_1005_ = lean_int_dec_lt(v_k_1003_, v_k_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v_b_986_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_k_987_);
v___x_1007_ = v___x_995_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_size_989_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_k_987_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1008_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1008_, 4, v_r_993_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
else
{
lean_object* v___x_1010_; 
lean_dec(v_v_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 2, v_b_986_);
lean_ctor_set(v___x_995_, 1, v_k_987_);
v___x_1010_ = v___x_995_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_size_989_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_987_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_b_986_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_l_992_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_993_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1012_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__1(v_b_986_, v_k_987_, v_l_992_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 3, v___x_1012_);
v___x_1014_ = v___x_995_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_size_989_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_k_990_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_v_991_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_r_993_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
else
{
lean_dec(v_k_987_);
lean_dec_ref(v_b_986_);
return v_t_988_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_nat_to_int(v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3(lean_object* v_init_1019_, lean_object* v_x_1020_){
_start:
{
if (lean_obj_tag(v_x_1020_) == 0)
{
lean_object* v_v_1021_; lean_object* v_l_1022_; lean_object* v_r_1023_; lean_object* v___x_1024_; lean_object* v_ordered_1025_; lean_object* v_index_1026_; lean_object* v_lin_1027_; lean_object* v___x_1028_; 
v_v_1021_ = lean_ctor_get(v_x_1020_, 2);
lean_inc(v_v_1021_);
v_l_1022_ = lean_ctor_get(v_x_1020_, 3);
lean_inc(v_l_1022_);
v_r_1023_ = lean_ctor_get(v_x_1020_, 4);
lean_inc(v_r_1023_);
lean_dec_ref_known(v_x_1020_, 5);
v___x_1024_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3(v_init_1019_, v_l_1022_);
v_ordered_1025_ = lean_ctor_get(v___x_1024_, 0);
v_index_1026_ = lean_ctor_get(v___x_1024_, 1);
v_lin_1027_ = lean_ctor_get(v_v_1021_, 0);
v___x_1028_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f_spec__0___redArg(v_index_1026_, v_lin_1027_);
if (lean_obj_tag(v___x_1028_) == 1)
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
lean_inc_ref(v_index_1026_);
lean_inc(v_ordered_1025_);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; lean_object* v_unused_1040_; 
v_unused_1039_ = lean_ctor_get(v___x_1024_, 1);
lean_dec(v_unused_1039_);
v_unused_1040_ = lean_ctor_get(v___x_1024_, 0);
lean_dec(v_unused_1040_);
v___x_1030_ = v___x_1024_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___x_1024_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_val_1032_; lean_object* v___x_1033_; lean_object* v___x_1035_; 
v_val_1032_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1028_, 1);
v___x_1033_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__1(v_v_1021_, v_val_1032_, v_ordered_1025_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_index_1026_);
v___x_1035_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
v_init_1019_ = v___x_1035_;
v_x_1020_ = v_r_1023_;
goto _start;
}
}
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v___x_1028_);
v___x_1041_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_ordered_1025_, v___x_1041_);
v___x_1043_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0);
v___x_1044_ = lean_int_add(v___x_1042_, v___x_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v___x_1024_, v___x_1044_, v_v_1021_);
v_init_1019_ = v___x_1045_;
v_x_1020_ = v_r_1023_;
goto _start;
}
}
else
{
return v_init_1019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(lean_object* v_k_1047_, lean_object* v_t_1048_){
_start:
{
if (lean_obj_tag(v_t_1048_) == 0)
{
lean_object* v_k_1049_; lean_object* v_v_1050_; lean_object* v_l_1051_; lean_object* v_r_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1707_; 
v_k_1049_ = lean_ctor_get(v_t_1048_, 1);
v_v_1050_ = lean_ctor_get(v_t_1048_, 2);
v_l_1051_ = lean_ctor_get(v_t_1048_, 3);
v_r_1052_ = lean_ctor_get(v_t_1048_, 4);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_t_1048_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v_t_1048_, 0);
lean_dec(v_unused_1708_);
v___x_1054_ = v_t_1048_;
v_isShared_1055_ = v_isSharedCheck_1707_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_r_1052_);
lean_inc(v_l_1051_);
lean_inc(v_v_1050_);
lean_inc(v_k_1049_);
lean_dec(v_t_1048_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1707_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_int_dec_lt(v_k_1047_, v_k_1049_);
if (v___x_1056_ == 0)
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_int_dec_eq(v_k_1047_, v_k_1049_);
if (v___x_1057_ == 0)
{
lean_object* v_impl_1058_; lean_object* v___x_1059_; 
v_impl_1058_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(v_k_1047_, v_r_1052_);
v___x_1059_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1058_) == 0)
{
if (lean_obj_tag(v_l_1051_) == 0)
{
lean_object* v_size_1060_; lean_object* v_size_1061_; lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v_l_1064_; lean_object* v_r_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_size_1060_ = lean_ctor_get(v_impl_1058_, 0);
v_size_1061_ = lean_ctor_get(v_l_1051_, 0);
v_k_1062_ = lean_ctor_get(v_l_1051_, 1);
v_v_1063_ = lean_ctor_get(v_l_1051_, 2);
v_l_1064_ = lean_ctor_get(v_l_1051_, 3);
v_r_1065_ = lean_ctor_get(v_l_1051_, 4);
lean_inc(v_r_1065_);
v___x_1066_ = lean_unsigned_to_nat(3u);
v___x_1067_ = lean_nat_mul(v___x_1066_, v_size_1060_);
v___x_1068_ = lean_nat_dec_lt(v___x_1067_, v_size_1061_);
lean_dec(v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec(v_r_1065_);
v___x_1069_ = lean_nat_add(v___x_1059_, v_size_1061_);
v___x_1070_ = lean_nat_add(v___x_1069_, v_size_1060_);
lean_dec(v___x_1069_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_impl_1058_);
lean_ctor_set(v___x_1054_, 0, v___x_1070_);
v___x_1072_ = v___x_1054_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_impl_1058_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1139_; 
lean_inc(v_l_1064_);
lean_inc(v_v_1063_);
lean_inc(v_k_1062_);
lean_inc(v_size_1061_);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; lean_object* v_unused_1141_; lean_object* v_unused_1142_; lean_object* v_unused_1143_; lean_object* v_unused_1144_; 
v_unused_1140_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1140_);
v_unused_1141_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1141_);
v_unused_1142_ = lean_ctor_get(v_l_1051_, 2);
lean_dec(v_unused_1142_);
v_unused_1143_ = lean_ctor_get(v_l_1051_, 1);
lean_dec(v_unused_1143_);
v_unused_1144_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1144_);
v___x_1075_ = v_l_1051_;
v_isShared_1076_ = v_isSharedCheck_1139_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v_l_1051_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1139_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_size_1077_; lean_object* v_size_1078_; lean_object* v_k_1079_; lean_object* v_v_1080_; lean_object* v_l_1081_; lean_object* v_r_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_size_1077_ = lean_ctor_get(v_l_1064_, 0);
v_size_1078_ = lean_ctor_get(v_r_1065_, 0);
v_k_1079_ = lean_ctor_get(v_r_1065_, 1);
v_v_1080_ = lean_ctor_get(v_r_1065_, 2);
v_l_1081_ = lean_ctor_get(v_r_1065_, 3);
v_r_1082_ = lean_ctor_get(v_r_1065_, 4);
v___x_1083_ = lean_unsigned_to_nat(2u);
v___x_1084_ = lean_nat_mul(v___x_1083_, v_size_1077_);
v___x_1085_ = lean_nat_dec_lt(v_size_1078_, v___x_1084_);
lean_dec(v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1114_; 
lean_inc(v_r_1082_);
lean_inc(v_l_1081_);
lean_inc(v_v_1080_);
lean_inc(v_k_1079_);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_r_1065_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1115_ = lean_ctor_get(v_r_1065_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_r_1065_, 3);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_1065_, 2);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_1065_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_r_1065_, 0);
lean_dec(v_unused_1119_);
v___x_1087_ = v_r_1065_;
v_isShared_1088_ = v_isSharedCheck_1114_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_r_1065_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1114_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___x_1102_; lean_object* v___y_1104_; 
v___x_1089_ = lean_nat_add(v___x_1059_, v_size_1061_);
lean_dec(v_size_1061_);
v___x_1090_ = lean_nat_add(v___x_1089_, v_size_1060_);
lean_dec(v___x_1089_);
v___x_1102_ = lean_nat_add(v___x_1059_, v_size_1077_);
if (lean_obj_tag(v_l_1081_) == 0)
{
lean_object* v_size_1112_; 
v_size_1112_ = lean_ctor_get(v_l_1081_, 0);
lean_inc(v_size_1112_);
v___y_1104_ = v_size_1112_;
goto v___jp_1103_;
}
else
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_unsigned_to_nat(0u);
v___y_1104_ = v___x_1113_;
goto v___jp_1103_;
}
v___jp_1091_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_nat_add(v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 4, v_impl_1058_);
lean_ctor_set(v___x_1087_, 3, v_r_1082_);
lean_ctor_set(v___x_1087_, 2, v_v_1050_);
lean_ctor_set(v___x_1087_, 1, v_k_1049_);
lean_ctor_set(v___x_1087_, 0, v___x_1095_);
v___x_1097_ = v___x_1087_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1095_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_r_1082_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_impl_1058_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 4, v___x_1097_);
lean_ctor_set(v___x_1075_, 3, v___y_1092_);
lean_ctor_set(v___x_1075_, 2, v_v_1080_);
lean_ctor_set(v___x_1075_, 1, v_k_1079_);
lean_ctor_set(v___x_1075_, 0, v___x_1090_);
v___x_1099_ = v___x_1075_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_k_1079_);
lean_ctor_set(v_reuseFailAlloc_1100_, 2, v_v_1080_);
lean_ctor_set(v_reuseFailAlloc_1100_, 3, v___y_1092_);
lean_ctor_set(v_reuseFailAlloc_1100_, 4, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
v___jp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_nat_add(v___x_1102_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec(v___x_1102_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_l_1081_);
lean_ctor_set(v___x_1054_, 3, v_l_1064_);
lean_ctor_set(v___x_1054_, 2, v_v_1063_);
lean_ctor_set(v___x_1054_, 1, v_k_1062_);
lean_ctor_set(v___x_1054_, 0, v___x_1105_);
v___x_1107_ = v___x_1054_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_k_1062_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_v_1063_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_l_1064_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_l_1081_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_nat_add(v___x_1059_, v_size_1060_);
if (lean_obj_tag(v_r_1082_) == 0)
{
lean_object* v_size_1109_; 
v_size_1109_ = lean_ctor_get(v_r_1082_, 0);
lean_inc(v_size_1109_);
v___y_1092_ = v___x_1107_;
v___y_1093_ = v___x_1108_;
v___y_1094_ = v_size_1109_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_unsigned_to_nat(0u);
v___y_1092_ = v___x_1107_;
v___y_1093_ = v___x_1108_;
v___y_1094_ = v___x_1110_;
goto v___jp_1091_;
}
}
}
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_del_object(v___x_1054_);
v___x_1120_ = lean_nat_add(v___x_1059_, v_size_1061_);
lean_dec(v_size_1061_);
v___x_1121_ = lean_nat_add(v___x_1120_, v_size_1060_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_nat_add(v___x_1059_, v_size_1060_);
v___x_1123_ = lean_nat_add(v___x_1122_, v_size_1078_);
lean_dec(v___x_1122_);
lean_inc_ref(v_impl_1058_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 4, v_impl_1058_);
lean_ctor_set(v___x_1075_, 3, v_r_1065_);
lean_ctor_set(v___x_1075_, 2, v_v_1050_);
lean_ctor_set(v___x_1075_, 1, v_k_1049_);
lean_ctor_set(v___x_1075_, 0, v___x_1123_);
v___x_1125_ = v___x_1075_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_r_1065_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_impl_1058_);
v___x_1125_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
v_isSharedCheck_1132_ = !lean_is_exclusive(v_impl_1058_);
if (v_isSharedCheck_1132_ == 0)
{
lean_object* v_unused_1133_; lean_object* v_unused_1134_; lean_object* v_unused_1135_; lean_object* v_unused_1136_; lean_object* v_unused_1137_; 
v_unused_1133_ = lean_ctor_get(v_impl_1058_, 4);
lean_dec(v_unused_1133_);
v_unused_1134_ = lean_ctor_get(v_impl_1058_, 3);
lean_dec(v_unused_1134_);
v_unused_1135_ = lean_ctor_get(v_impl_1058_, 2);
lean_dec(v_unused_1135_);
v_unused_1136_ = lean_ctor_get(v_impl_1058_, 1);
lean_dec(v_unused_1136_);
v_unused_1137_ = lean_ctor_get(v_impl_1058_, 0);
lean_dec(v_unused_1137_);
v___x_1127_ = v_impl_1058_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v_impl_1058_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___x_1125_);
lean_ctor_set(v___x_1127_, 3, v_l_1064_);
lean_ctor_set(v___x_1127_, 2, v_v_1063_);
lean_ctor_set(v___x_1127_, 1, v_k_1062_);
lean_ctor_set(v___x_1127_, 0, v___x_1121_);
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_1062_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_1063_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_l_1064_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v___x_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_size_1145_ = lean_ctor_get(v_impl_1058_, 0);
v___x_1146_ = lean_nat_add(v___x_1059_, v_size_1145_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_impl_1058_);
lean_ctor_set(v___x_1054_, 0, v___x_1146_);
v___x_1148_ = v___x_1054_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1149_, 4, v_impl_1058_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
if (lean_obj_tag(v_l_1051_) == 0)
{
lean_object* v_l_1150_; 
v_l_1150_ = lean_ctor_get(v_l_1051_, 3);
if (lean_obj_tag(v_l_1150_) == 0)
{
lean_object* v_r_1151_; 
lean_inc_ref(v_l_1150_);
v_r_1151_ = lean_ctor_get(v_l_1051_, 4);
lean_inc(v_r_1151_);
if (lean_obj_tag(v_r_1151_) == 0)
{
lean_object* v_size_1152_; lean_object* v_k_1153_; lean_object* v_v_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1167_; 
v_size_1152_ = lean_ctor_get(v_l_1051_, 0);
v_k_1153_ = lean_ctor_get(v_l_1051_, 1);
v_v_1154_ = lean_ctor_get(v_l_1051_, 2);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1168_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1169_);
v___x_1156_ = v_l_1051_;
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_v_1154_);
lean_inc(v_k_1153_);
lean_inc(v_size_1152_);
lean_dec(v_l_1051_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1167_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_size_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
v_size_1158_ = lean_ctor_get(v_r_1151_, 0);
v___x_1159_ = lean_nat_add(v___x_1059_, v_size_1152_);
lean_dec(v_size_1152_);
v___x_1160_ = lean_nat_add(v___x_1059_, v_size_1158_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 4, v_impl_1058_);
lean_ctor_set(v___x_1156_, 3, v_r_1151_);
lean_ctor_set(v___x_1156_, 2, v_v_1050_);
lean_ctor_set(v___x_1156_, 1, v_k_1049_);
lean_ctor_set(v___x_1156_, 0, v___x_1160_);
v___x_1162_ = v___x_1156_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_r_1151_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_impl_1058_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1162_);
lean_ctor_set(v___x_1054_, 3, v_l_1150_);
lean_ctor_set(v___x_1054_, 2, v_v_1154_);
lean_ctor_set(v___x_1054_, 1, v_k_1153_);
lean_ctor_set(v___x_1054_, 0, v___x_1159_);
v___x_1164_ = v___x_1054_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1153_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1154_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_l_1150_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v_k_1170_; lean_object* v_v_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1182_; 
v_k_1170_ = lean_ctor_get(v_l_1051_, 1);
v_v_1171_ = lean_ctor_get(v_l_1051_, 2);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1183_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1183_);
v_unused_1184_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1185_);
v___x_1173_ = v_l_1051_;
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_v_1171_);
lean_inc(v_k_1170_);
lean_dec(v_l_1051_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_unsigned_to_nat(3u);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 3, v_r_1151_);
lean_ctor_set(v___x_1173_, 2, v_v_1050_);
lean_ctor_set(v___x_1173_, 1, v_k_1049_);
lean_ctor_set(v___x_1173_, 0, v___x_1059_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_r_1151_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_r_1151_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1177_);
lean_ctor_set(v___x_1054_, 3, v_l_1150_);
lean_ctor_set(v___x_1054_, 2, v_v_1171_);
lean_ctor_set(v___x_1054_, 1, v_k_1170_);
lean_ctor_set(v___x_1054_, 0, v___x_1175_);
v___x_1179_ = v___x_1054_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_k_1170_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_v_1171_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_l_1150_);
lean_ctor_set(v_reuseFailAlloc_1180_, 4, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
else
{
lean_object* v_r_1186_; 
v_r_1186_ = lean_ctor_get(v_l_1051_, 4);
lean_inc(v_r_1186_);
if (lean_obj_tag(v_r_1186_) == 0)
{
lean_object* v_k_1187_; lean_object* v_v_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1211_; 
lean_inc(v_l_1150_);
v_k_1187_ = lean_ctor_get(v_l_1051_, 1);
v_v_1188_ = lean_ctor_get(v_l_1051_, 2);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; lean_object* v_unused_1214_; 
v_unused_1212_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1214_);
v___x_1190_ = v_l_1051_;
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_v_1188_);
lean_inc(v_k_1187_);
lean_dec(v_l_1051_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1211_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_k_1192_; lean_object* v_v_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1207_; 
v_k_1192_ = lean_ctor_get(v_r_1186_, 1);
v_v_1193_ = lean_ctor_get(v_r_1186_, 2);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_r_1186_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; lean_object* v_unused_1210_; 
v_unused_1208_ = lean_ctor_get(v_r_1186_, 4);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_r_1186_, 3);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_r_1186_, 0);
lean_dec(v_unused_1210_);
v___x_1195_ = v_r_1186_;
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_v_1193_);
lean_inc(v_k_1192_);
lean_dec(v_r_1186_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1207_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_unsigned_to_nat(3u);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 4, v_l_1150_);
lean_ctor_set(v___x_1195_, 3, v_l_1150_);
lean_ctor_set(v___x_1195_, 2, v_v_1188_);
lean_ctor_set(v___x_1195_, 1, v_k_1187_);
lean_ctor_set(v___x_1195_, 0, v___x_1059_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1187_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1188_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_l_1150_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_l_1150_);
v___x_1199_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v_l_1150_);
lean_ctor_set(v___x_1190_, 2, v_v_1050_);
lean_ctor_set(v___x_1190_, 1, v_k_1049_);
lean_ctor_set(v___x_1190_, 0, v___x_1059_);
v___x_1201_ = v___x_1190_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_l_1150_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v_l_1150_);
v___x_1201_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1203_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1201_);
lean_ctor_set(v___x_1054_, 3, v___x_1199_);
lean_ctor_set(v___x_1054_, 2, v_v_1193_);
lean_ctor_set(v___x_1054_, 1, v_k_1192_);
lean_ctor_set(v___x_1054_, 0, v___x_1197_);
v___x_1203_ = v___x_1054_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_k_1192_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_v_1193_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_unsigned_to_nat(2u);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_r_1186_);
lean_ctor_set(v___x_1054_, 0, v___x_1215_);
v___x_1217_ = v___x_1054_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_r_1186_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v___x_1220_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_l_1051_);
lean_ctor_set(v___x_1054_, 0, v___x_1059_);
v___x_1220_ = v___x_1054_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1221_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1221_, 4, v_l_1051_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_del_object(v___x_1054_);
lean_dec(v_v_1050_);
lean_dec(v_k_1049_);
if (lean_obj_tag(v_l_1051_) == 0)
{
if (lean_obj_tag(v_r_1052_) == 0)
{
lean_object* v_size_1222_; lean_object* v_k_1223_; lean_object* v_v_1224_; lean_object* v_l_1225_; lean_object* v_r_1226_; lean_object* v_size_1227_; lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v_l_1230_; lean_object* v_r_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v_size_1222_ = lean_ctor_get(v_l_1051_, 0);
v_k_1223_ = lean_ctor_get(v_l_1051_, 1);
v_v_1224_ = lean_ctor_get(v_l_1051_, 2);
v_l_1225_ = lean_ctor_get(v_l_1051_, 3);
v_r_1226_ = lean_ctor_get(v_l_1051_, 4);
lean_inc(v_r_1226_);
v_size_1227_ = lean_ctor_get(v_r_1052_, 0);
v_k_1228_ = lean_ctor_get(v_r_1052_, 1);
v_v_1229_ = lean_ctor_get(v_r_1052_, 2);
v_l_1230_ = lean_ctor_get(v_r_1052_, 3);
lean_inc(v_l_1230_);
v_r_1231_ = lean_ctor_get(v_r_1052_, 4);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_dec_lt(v_size_1222_, v_size_1227_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_l_1225_);
lean_inc(v_v_1224_);
lean_inc(v_k_1223_);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1369_ == 0)
{
lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; 
v_unused_1370_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_l_1051_, 2);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_l_1051_, 1);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1374_);
v___x_1235_ = v_l_1051_;
v_isShared_1236_ = v_isSharedCheck_1369_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v_l_1051_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1369_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v_tree_1238_; 
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1223_, v_v_1224_, v_l_1225_, v_r_1226_);
v_tree_1238_ = lean_ctor_get(v___x_1237_, 2);
if (lean_obj_tag(v_tree_1238_) == 0)
{
lean_object* v_k_1239_; lean_object* v_v_1240_; lean_object* v_size_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
lean_inc_ref(v_tree_1238_);
v_k_1239_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_k_1239_);
v_v_1240_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_v_1240_);
lean_dec_ref(v___x_1237_);
v_size_1241_ = lean_ctor_get(v_tree_1238_, 0);
v___x_1242_ = lean_unsigned_to_nat(3u);
v___x_1243_ = lean_nat_mul(v___x_1242_, v_size_1241_);
v___x_1244_ = lean_nat_dec_lt(v___x_1243_, v_size_1227_);
lean_dec(v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
lean_dec(v_l_1230_);
v___x_1245_ = lean_nat_add(v___x_1232_, v_size_1241_);
v___x_1246_ = lean_nat_add(v___x_1245_, v_size_1227_);
lean_dec(v___x_1245_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_r_1052_);
lean_ctor_set(v___x_1235_, 3, v_tree_1238_);
lean_ctor_set(v___x_1235_, 2, v_v_1240_);
lean_ctor_set(v___x_1235_, 1, v_k_1239_);
lean_ctor_set(v___x_1235_, 0, v___x_1246_);
v___x_1248_ = v___x_1235_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_tree_1238_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_r_1052_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
else
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1304_; 
lean_inc(v_r_1231_);
lean_inc(v_v_1229_);
lean_inc(v_k_1228_);
lean_inc(v_size_1227_);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1304_ == 0)
{
lean_object* v_unused_1305_; lean_object* v_unused_1306_; lean_object* v_unused_1307_; lean_object* v_unused_1308_; lean_object* v_unused_1309_; 
v_unused_1305_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1305_);
v_unused_1306_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1306_);
v_unused_1307_ = lean_ctor_get(v_r_1052_, 2);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_r_1052_, 1);
lean_dec(v_unused_1308_);
v_unused_1309_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1309_);
v___x_1251_ = v_r_1052_;
v_isShared_1252_ = v_isSharedCheck_1304_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v_r_1052_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1304_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_size_1253_; lean_object* v_k_1254_; lean_object* v_v_1255_; lean_object* v_l_1256_; lean_object* v_r_1257_; lean_object* v_size_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_size_1253_ = lean_ctor_get(v_l_1230_, 0);
v_k_1254_ = lean_ctor_get(v_l_1230_, 1);
v_v_1255_ = lean_ctor_get(v_l_1230_, 2);
v_l_1256_ = lean_ctor_get(v_l_1230_, 3);
v_r_1257_ = lean_ctor_get(v_l_1230_, 4);
v_size_1258_ = lean_ctor_get(v_r_1231_, 0);
v___x_1259_ = lean_unsigned_to_nat(2u);
v___x_1260_ = lean_nat_mul(v___x_1259_, v_size_1258_);
v___x_1261_ = lean_nat_dec_lt(v_size_1253_, v___x_1260_);
lean_dec(v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1289_; 
lean_inc(v_r_1257_);
lean_inc(v_l_1256_);
lean_inc(v_v_1255_);
lean_inc(v_k_1254_);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_l_1230_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; lean_object* v_unused_1291_; lean_object* v_unused_1292_; lean_object* v_unused_1293_; lean_object* v_unused_1294_; 
v_unused_1290_ = lean_ctor_get(v_l_1230_, 4);
lean_dec(v_unused_1290_);
v_unused_1291_ = lean_ctor_get(v_l_1230_, 3);
lean_dec(v_unused_1291_);
v_unused_1292_ = lean_ctor_get(v_l_1230_, 2);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_l_1230_, 1);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_l_1230_, 0);
lean_dec(v_unused_1294_);
v___x_1263_ = v_l_1230_;
v_isShared_1264_ = v_isSharedCheck_1289_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_l_1230_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1289_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1279_; 
v___x_1265_ = lean_nat_add(v___x_1232_, v_size_1241_);
v___x_1266_ = lean_nat_add(v___x_1265_, v_size_1227_);
lean_dec(v_size_1227_);
if (lean_obj_tag(v_l_1256_) == 0)
{
lean_object* v_size_1287_; 
v_size_1287_ = lean_ctor_get(v_l_1256_, 0);
lean_inc(v_size_1287_);
v___y_1279_ = v_size_1287_;
goto v___jp_1278_;
}
else
{
lean_object* v___x_1288_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___y_1279_ = v___x_1288_;
goto v___jp_1278_;
}
v___jp_1267_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_nat_add(v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec(v___y_1269_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 4, v_r_1231_);
lean_ctor_set(v___x_1263_, 3, v_r_1257_);
lean_ctor_set(v___x_1263_, 2, v_v_1229_);
lean_ctor_set(v___x_1263_, 1, v_k_1228_);
lean_ctor_set(v___x_1263_, 0, v___x_1271_);
v___x_1273_ = v___x_1263_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1257_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_r_1231_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 4, v___x_1273_);
lean_ctor_set(v___x_1251_, 3, v___y_1268_);
lean_ctor_set(v___x_1251_, 2, v_v_1255_);
lean_ctor_set(v___x_1251_, 1, v_k_1254_);
lean_ctor_set(v___x_1251_, 0, v___x_1266_);
v___x_1275_ = v___x_1251_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_k_1254_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_v_1255_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v___y_1268_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
v___jp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_nat_add(v___x_1265_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec(v___x_1265_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_l_1256_);
lean_ctor_set(v___x_1235_, 3, v_tree_1238_);
lean_ctor_set(v___x_1235_, 2, v_v_1240_);
lean_ctor_set(v___x_1235_, 1, v_k_1239_);
lean_ctor_set(v___x_1235_, 0, v___x_1280_);
v___x_1282_ = v___x_1235_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_tree_1238_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_l_1256_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_nat_add(v___x_1232_, v_size_1258_);
if (lean_obj_tag(v_r_1257_) == 0)
{
lean_object* v_size_1284_; 
v_size_1284_ = lean_ctor_get(v_r_1257_, 0);
lean_inc(v_size_1284_);
v___y_1268_ = v___x_1282_;
v___y_1269_ = v___x_1283_;
v___y_1270_ = v_size_1284_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___y_1268_ = v___x_1282_;
v___y_1269_ = v___x_1283_;
v___y_1270_ = v___x_1285_;
goto v___jp_1267_;
}
}
}
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1295_ = lean_nat_add(v___x_1232_, v_size_1241_);
v___x_1296_ = lean_nat_add(v___x_1295_, v_size_1227_);
lean_dec(v_size_1227_);
v___x_1297_ = lean_nat_add(v___x_1295_, v_size_1253_);
lean_dec(v___x_1295_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 4, v_l_1230_);
lean_ctor_set(v___x_1251_, 3, v_tree_1238_);
lean_ctor_set(v___x_1251_, 2, v_v_1240_);
lean_ctor_set(v___x_1251_, 1, v_k_1239_);
lean_ctor_set(v___x_1251_, 0, v___x_1297_);
v___x_1299_ = v___x_1251_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_tree_1238_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_l_1230_);
v___x_1299_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1301_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_r_1231_);
lean_ctor_set(v___x_1235_, 3, v___x_1299_);
lean_ctor_set(v___x_1235_, 2, v_v_1229_);
lean_ctor_set(v___x_1235_, 1, v_k_1228_);
lean_ctor_set(v___x_1235_, 0, v___x_1296_);
v___x_1301_ = v___x_1235_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1231_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
}
else
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1363_; 
lean_inc(v_r_1231_);
lean_inc(v_v_1229_);
lean_inc(v_k_1228_);
lean_inc(v_size_1227_);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; lean_object* v_unused_1368_; 
v_unused_1364_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_r_1052_, 2);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_r_1052_, 1);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1368_);
v___x_1311_ = v_r_1052_;
v_isShared_1312_ = v_isSharedCheck_1363_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_r_1052_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1363_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
if (lean_obj_tag(v_l_1230_) == 0)
{
if (lean_obj_tag(v_r_1231_) == 0)
{
lean_object* v_k_1313_; lean_object* v_v_1314_; lean_object* v_size_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_inc(v_tree_1238_);
v_k_1313_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_k_1313_);
v_v_1314_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_v_1314_);
lean_dec_ref(v___x_1237_);
v_size_1315_ = lean_ctor_get(v_l_1230_, 0);
v___x_1316_ = lean_nat_add(v___x_1232_, v_size_1227_);
lean_dec(v_size_1227_);
v___x_1317_ = lean_nat_add(v___x_1232_, v_size_1315_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v_l_1230_);
lean_ctor_set(v___x_1311_, 3, v_tree_1238_);
lean_ctor_set(v___x_1311_, 2, v_v_1314_);
lean_ctor_set(v___x_1311_, 1, v_k_1313_);
lean_ctor_set(v___x_1311_, 0, v___x_1317_);
v___x_1319_ = v___x_1311_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1313_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_tree_1238_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_l_1230_);
v___x_1319_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1321_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_r_1231_);
lean_ctor_set(v___x_1235_, 3, v___x_1319_);
lean_ctor_set(v___x_1235_, 2, v_v_1229_);
lean_ctor_set(v___x_1235_, 1, v_k_1228_);
lean_ctor_set(v___x_1235_, 0, v___x_1316_);
v___x_1321_ = v___x_1235_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 4, v_r_1231_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v_k_1326_; lean_object* v_v_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_size_1227_);
v_k_1324_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_k_1324_);
v_v_1325_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_v_1325_);
lean_dec_ref(v___x_1237_);
v_k_1326_ = lean_ctor_get(v_l_1230_, 1);
v_v_1327_ = lean_ctor_get(v_l_1230_, 2);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_l_1230_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; lean_object* v_unused_1343_; lean_object* v_unused_1344_; 
v_unused_1342_ = lean_ctor_get(v_l_1230_, 4);
lean_dec(v_unused_1342_);
v_unused_1343_ = lean_ctor_get(v_l_1230_, 3);
lean_dec(v_unused_1343_);
v_unused_1344_ = lean_ctor_get(v_l_1230_, 0);
lean_dec(v_unused_1344_);
v___x_1329_ = v_l_1230_;
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_v_1327_);
lean_inc(v_k_1326_);
lean_dec(v_l_1230_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1341_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_unsigned_to_nat(3u);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 4, v_r_1231_);
lean_ctor_set(v___x_1329_, 3, v_r_1231_);
lean_ctor_set(v___x_1329_, 2, v_v_1325_);
lean_ctor_set(v___x_1329_, 1, v_k_1324_);
lean_ctor_set(v___x_1329_, 0, v___x_1232_);
v___x_1333_ = v___x_1329_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1325_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1231_);
v___x_1333_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 3, v_r_1231_);
lean_ctor_set(v___x_1311_, 0, v___x_1232_);
v___x_1335_ = v___x_1311_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_r_1231_);
v___x_1335_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1337_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v___x_1335_);
lean_ctor_set(v___x_1235_, 3, v___x_1333_);
lean_ctor_set(v___x_1235_, 2, v_v_1327_);
lean_ctor_set(v___x_1235_, 1, v_k_1326_);
lean_ctor_set(v___x_1235_, 0, v___x_1331_);
v___x_1337_ = v___x_1235_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_k_1326_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_v_1327_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1231_) == 0)
{
lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_dec(v_size_1227_);
v_k_1345_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_k_1345_);
v_v_1346_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_v_1346_);
lean_dec_ref(v___x_1237_);
v___x_1347_ = lean_unsigned_to_nat(3u);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v_l_1230_);
lean_ctor_set(v___x_1311_, 2, v_v_1346_);
lean_ctor_set(v___x_1311_, 1, v_k_1345_);
lean_ctor_set(v___x_1311_, 0, v___x_1232_);
v___x_1349_ = v___x_1311_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_k_1345_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_v_1346_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_l_1230_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v_l_1230_);
v___x_1349_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1351_; 
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_r_1231_);
lean_ctor_set(v___x_1235_, 3, v___x_1349_);
lean_ctor_set(v___x_1235_, 2, v_v_1229_);
lean_ctor_set(v___x_1235_, 1, v_k_1228_);
lean_ctor_set(v___x_1235_, 0, v___x_1347_);
v___x_1351_ = v___x_1235_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_r_1231_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_object* v_k_1354_; lean_object* v_v_1355_; lean_object* v___x_1357_; 
v_k_1354_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_k_1354_);
v_v_1355_ = lean_ctor_get(v___x_1237_, 1);
lean_inc(v_v_1355_);
lean_dec_ref(v___x_1237_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 3, v_r_1231_);
v___x_1357_ = v___x_1311_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_size_1227_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_k_1228_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_v_1229_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_r_1231_);
v___x_1357_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_unsigned_to_nat(2u);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v___x_1357_);
lean_ctor_set(v___x_1235_, 3, v_r_1231_);
lean_ctor_set(v___x_1235_, 2, v_v_1355_);
lean_ctor_set(v___x_1235_, 1, v_k_1354_);
lean_ctor_set(v___x_1235_, 0, v___x_1358_);
v___x_1360_ = v___x_1235_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_r_1231_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v___x_1357_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
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
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1527_; 
lean_inc(v_r_1231_);
lean_inc(v_v_1229_);
lean_inc(v_k_1228_);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; 
v_unused_1528_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_r_1052_, 2);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_r_1052_, 1);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1532_);
v___x_1376_ = v_r_1052_;
v_isShared_1377_ = v_isSharedCheck_1527_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_r_1052_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1527_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v_tree_1379_; 
v___x_1378_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1228_, v_v_1229_, v_l_1230_, v_r_1231_);
v_tree_1379_ = lean_ctor_get(v___x_1378_, 2);
lean_inc(v_tree_1379_);
if (lean_obj_tag(v_tree_1379_) == 0)
{
lean_object* v_k_1380_; lean_object* v_v_1381_; lean_object* v_size_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; uint8_t v___x_1385_; 
v_k_1380_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_k_1380_);
v_v_1381_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_v_1381_);
lean_dec_ref(v___x_1378_);
v_size_1382_ = lean_ctor_get(v_tree_1379_, 0);
v___x_1383_ = lean_unsigned_to_nat(3u);
v___x_1384_ = lean_nat_mul(v___x_1383_, v_size_1382_);
v___x_1385_ = lean_nat_dec_lt(v___x_1384_, v_size_1222_);
lean_dec(v___x_1384_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_dec(v_r_1226_);
v___x_1386_ = lean_nat_add(v___x_1232_, v_size_1222_);
v___x_1387_ = lean_nat_add(v___x_1386_, v_size_1382_);
lean_dec(v___x_1386_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_tree_1379_);
lean_ctor_set(v___x_1376_, 3, v_l_1051_);
lean_ctor_set(v___x_1376_, 2, v_v_1381_);
lean_ctor_set(v___x_1376_, 1, v_k_1380_);
lean_ctor_set(v___x_1376_, 0, v___x_1387_);
v___x_1389_ = v___x_1376_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_tree_1379_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1456_; 
lean_inc(v_l_1225_);
lean_inc(v_v_1224_);
lean_inc(v_k_1223_);
lean_inc(v_size_1222_);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; lean_object* v_unused_1459_; lean_object* v_unused_1460_; lean_object* v_unused_1461_; 
v_unused_1457_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1458_);
v_unused_1459_ = lean_ctor_get(v_l_1051_, 2);
lean_dec(v_unused_1459_);
v_unused_1460_ = lean_ctor_get(v_l_1051_, 1);
lean_dec(v_unused_1460_);
v_unused_1461_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1461_);
v___x_1392_ = v_l_1051_;
v_isShared_1393_ = v_isSharedCheck_1456_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_l_1051_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1456_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_size_1394_; lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_l_1398_; lean_object* v_r_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; uint8_t v___x_1402_; 
v_size_1394_ = lean_ctor_get(v_l_1225_, 0);
v_size_1395_ = lean_ctor_get(v_r_1226_, 0);
v_k_1396_ = lean_ctor_get(v_r_1226_, 1);
v_v_1397_ = lean_ctor_get(v_r_1226_, 2);
v_l_1398_ = lean_ctor_get(v_r_1226_, 3);
v_r_1399_ = lean_ctor_get(v_r_1226_, 4);
v___x_1400_ = lean_unsigned_to_nat(2u);
v___x_1401_ = lean_nat_mul(v___x_1400_, v_size_1394_);
v___x_1402_ = lean_nat_dec_lt(v_size_1395_, v___x_1401_);
lean_dec(v___x_1401_);
if (v___x_1402_ == 0)
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_r_1399_);
lean_inc(v_l_1398_);
lean_inc(v_v_1397_);
lean_inc(v_k_1396_);
lean_del_object(v___x_1392_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_r_1226_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1441_ = lean_ctor_get(v_r_1226_, 4);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_r_1226_, 3);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_r_1226_, 2);
lean_dec(v_unused_1443_);
v_unused_1444_ = lean_ctor_get(v_r_1226_, 1);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_r_1226_, 0);
lean_dec(v_unused_1445_);
v___x_1404_ = v_r_1226_;
v_isShared_1405_ = v_isSharedCheck_1440_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_r_1226_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1440_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___x_1428_; lean_object* v___y_1430_; 
v___x_1406_ = lean_nat_add(v___x_1232_, v_size_1222_);
lean_dec(v_size_1222_);
v___x_1407_ = lean_nat_add(v___x_1406_, v_size_1382_);
lean_dec(v___x_1406_);
v___x_1428_ = lean_nat_add(v___x_1232_, v_size_1394_);
if (lean_obj_tag(v_l_1398_) == 0)
{
lean_object* v_size_1438_; 
v_size_1438_ = lean_ctor_get(v_l_1398_, 0);
lean_inc(v_size_1438_);
v___y_1430_ = v_size_1438_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1439_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___y_1430_ = v___x_1439_;
goto v___jp_1429_;
}
v___jp_1408_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_nat_add(v___y_1409_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec(v___y_1409_);
lean_inc_ref(v_tree_1379_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_tree_1379_);
lean_ctor_set(v___x_1404_, 3, v_r_1399_);
lean_ctor_set(v___x_1404_, 2, v_v_1381_);
lean_ctor_set(v___x_1404_, 1, v_k_1380_);
lean_ctor_set(v___x_1404_, 0, v___x_1412_);
v___x_1414_ = v___x_1404_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v_r_1399_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_tree_1379_);
v___x_1414_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_isSharedCheck_1421_ = !lean_is_exclusive(v_tree_1379_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; lean_object* v_unused_1426_; 
v_unused_1422_ = lean_ctor_get(v_tree_1379_, 4);
lean_dec(v_unused_1422_);
v_unused_1423_ = lean_ctor_get(v_tree_1379_, 3);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_tree_1379_, 2);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_tree_1379_, 1);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_tree_1379_, 0);
lean_dec(v_unused_1426_);
v___x_1416_ = v_tree_1379_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_tree_1379_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 4, v___x_1414_);
lean_ctor_set(v___x_1416_, 3, v___y_1410_);
lean_ctor_set(v___x_1416_, 2, v_v_1397_);
lean_ctor_set(v___x_1416_, 1, v_k_1396_);
lean_ctor_set(v___x_1416_, 0, v___x_1407_);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1396_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1397_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v___y_1410_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v___x_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
v___jp_1429_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1431_ = lean_nat_add(v___x_1428_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec(v___x_1428_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1398_);
lean_ctor_set(v___x_1376_, 3, v_l_1225_);
lean_ctor_set(v___x_1376_, 2, v_v_1224_);
lean_ctor_set(v___x_1376_, 1, v_k_1223_);
lean_ctor_set(v___x_1376_, 0, v___x_1431_);
v___x_1433_ = v___x_1376_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1223_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1224_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_l_1398_);
v___x_1433_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_nat_add(v___x_1232_, v_size_1382_);
if (lean_obj_tag(v_r_1399_) == 0)
{
lean_object* v_size_1435_; 
v_size_1435_ = lean_ctor_get(v_r_1399_, 0);
lean_inc(v_size_1435_);
v___y_1409_ = v___x_1434_;
v___y_1410_ = v___x_1433_;
v___y_1411_ = v_size_1435_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_unsigned_to_nat(0u);
v___y_1409_ = v___x_1434_;
v___y_1410_ = v___x_1433_;
v___y_1411_ = v___x_1436_;
goto v___jp_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1446_ = lean_nat_add(v___x_1232_, v_size_1222_);
lean_dec(v_size_1222_);
v___x_1447_ = lean_nat_add(v___x_1446_, v_size_1382_);
lean_dec(v___x_1446_);
v___x_1448_ = lean_nat_add(v___x_1232_, v_size_1382_);
v___x_1449_ = lean_nat_add(v___x_1448_, v_size_1395_);
lean_dec(v___x_1448_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_tree_1379_);
lean_ctor_set(v___x_1376_, 3, v_r_1226_);
lean_ctor_set(v___x_1376_, 2, v_v_1381_);
lean_ctor_set(v___x_1376_, 1, v_k_1380_);
lean_ctor_set(v___x_1376_, 0, v___x_1449_);
v___x_1451_ = v___x_1376_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1380_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1381_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_r_1226_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_tree_1379_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1451_);
lean_ctor_set(v___x_1392_, 0, v___x_1447_);
v___x_1453_ = v___x_1392_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1223_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1224_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1225_) == 0)
{
lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1485_; 
lean_inc_ref(v_l_1225_);
lean_inc(v_v_1224_);
lean_inc(v_k_1223_);
lean_inc(v_size_1222_);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1485_ == 0)
{
lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; lean_object* v_unused_1490_; 
v_unused_1486_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_l_1051_, 2);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_l_1051_, 1);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1490_);
v___x_1463_ = v_l_1051_;
v_isShared_1464_ = v_isSharedCheck_1485_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v_l_1051_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1485_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
if (lean_obj_tag(v_r_1226_) == 0)
{
lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v_size_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_k_1465_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_k_1465_);
v_v_1466_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_v_1466_);
lean_dec_ref(v___x_1378_);
v_size_1467_ = lean_ctor_get(v_r_1226_, 0);
v___x_1468_ = lean_nat_add(v___x_1232_, v_size_1222_);
lean_dec(v_size_1222_);
v___x_1469_ = lean_nat_add(v___x_1232_, v_size_1467_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_tree_1379_);
lean_ctor_set(v___x_1376_, 3, v_r_1226_);
lean_ctor_set(v___x_1376_, 2, v_v_1466_);
lean_ctor_set(v___x_1376_, 1, v_k_1465_);
lean_ctor_set(v___x_1376_, 0, v___x_1469_);
v___x_1471_ = v___x_1376_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1226_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_tree_1379_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1471_);
lean_ctor_set(v___x_1463_, 0, v___x_1468_);
v___x_1473_ = v___x_1463_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1223_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1224_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v_k_1476_; lean_object* v_v_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v_size_1222_);
v_k_1476_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_k_1476_);
v_v_1477_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_v_1477_);
lean_dec_ref(v___x_1378_);
v___x_1478_ = lean_unsigned_to_nat(3u);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1226_);
lean_ctor_set(v___x_1376_, 3, v_r_1226_);
lean_ctor_set(v___x_1376_, 2, v_v_1477_);
lean_ctor_set(v___x_1376_, 1, v_k_1476_);
lean_ctor_set(v___x_1376_, 0, v___x_1232_);
v___x_1480_ = v___x_1376_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_k_1476_);
lean_ctor_set(v_reuseFailAlloc_1484_, 2, v_v_1477_);
lean_ctor_set(v_reuseFailAlloc_1484_, 3, v_r_1226_);
lean_ctor_set(v_reuseFailAlloc_1484_, 4, v_r_1226_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 4, v___x_1480_);
lean_ctor_set(v___x_1463_, 0, v___x_1478_);
v___x_1482_ = v___x_1463_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1223_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1224_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1226_) == 0)
{
lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_l_1225_);
lean_inc(v_v_1224_);
lean_inc(v_k_1223_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_l_1051_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1516_ = lean_ctor_get(v_l_1051_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_l_1051_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_l_1051_, 2);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_l_1051_, 1);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_l_1051_, 0);
lean_dec(v_unused_1520_);
v___x_1492_ = v_l_1051_;
v_isShared_1493_ = v_isSharedCheck_1515_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v_l_1051_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1515_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v_k_1494_; lean_object* v_v_1495_; lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1511_; 
v_k_1494_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_k_1494_);
v_v_1495_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_v_1495_);
lean_dec_ref(v___x_1378_);
v_k_1496_ = lean_ctor_get(v_r_1226_, 1);
v_v_1497_ = lean_ctor_get(v_r_1226_, 2);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_r_1226_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1512_ = lean_ctor_get(v_r_1226_, 4);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_r_1226_, 3);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_r_1226_, 0);
lean_dec(v_unused_1514_);
v___x_1499_ = v_r_1226_;
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_v_1497_);
lean_inc(v_k_1496_);
lean_dec(v_r_1226_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1511_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1501_ = lean_unsigned_to_nat(3u);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 4, v_l_1225_);
lean_ctor_set(v___x_1499_, 3, v_l_1225_);
lean_ctor_set(v___x_1499_, 2, v_v_1224_);
lean_ctor_set(v___x_1499_, 1, v_k_1223_);
lean_ctor_set(v___x_1499_, 0, v___x_1232_);
v___x_1503_ = v___x_1499_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_k_1223_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_v_1224_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_l_1225_);
v___x_1503_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_l_1225_);
lean_ctor_set(v___x_1376_, 3, v_l_1225_);
lean_ctor_set(v___x_1376_, 2, v_v_1495_);
lean_ctor_set(v___x_1376_, 1, v_k_1494_);
lean_ctor_set(v___x_1376_, 0, v___x_1232_);
v___x_1505_ = v___x_1376_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_l_1225_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_l_1225_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 4, v___x_1505_);
lean_ctor_set(v___x_1492_, 3, v___x_1503_);
lean_ctor_set(v___x_1492_, 2, v_v_1497_);
lean_ctor_set(v___x_1492_, 1, v_k_1496_);
lean_ctor_set(v___x_1492_, 0, v___x_1501_);
v___x_1507_ = v___x_1492_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1497_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
}
}
else
{
lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v___x_1523_; lean_object* v___x_1525_; 
v_k_1521_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v___x_1378_, 1);
lean_inc(v_v_1522_);
lean_dec_ref(v___x_1378_);
v___x_1523_ = lean_unsigned_to_nat(2u);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v_r_1226_);
lean_ctor_set(v___x_1376_, 3, v_l_1051_);
lean_ctor_set(v___x_1376_, 2, v_v_1522_);
lean_ctor_set(v___x_1376_, 1, v_k_1521_);
lean_ctor_set(v___x_1376_, 0, v___x_1523_);
v___x_1525_ = v___x_1376_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1521_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1522_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_l_1051_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_r_1226_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
}
}
}
else
{
return v_l_1051_;
}
}
else
{
return v_r_1052_;
}
}
}
else
{
lean_object* v_impl_1533_; lean_object* v___x_1534_; 
v_impl_1533_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(v_k_1047_, v_l_1051_);
v___x_1534_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1533_) == 0)
{
if (lean_obj_tag(v_r_1052_) == 0)
{
lean_object* v_size_1535_; lean_object* v_size_1536_; lean_object* v_k_1537_; lean_object* v_v_1538_; lean_object* v_l_1539_; lean_object* v_r_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_size_1535_ = lean_ctor_get(v_impl_1533_, 0);
v_size_1536_ = lean_ctor_get(v_r_1052_, 0);
v_k_1537_ = lean_ctor_get(v_r_1052_, 1);
v_v_1538_ = lean_ctor_get(v_r_1052_, 2);
v_l_1539_ = lean_ctor_get(v_r_1052_, 3);
lean_inc(v_l_1539_);
v_r_1540_ = lean_ctor_get(v_r_1052_, 4);
v___x_1541_ = lean_unsigned_to_nat(3u);
v___x_1542_ = lean_nat_mul(v___x_1541_, v_size_1535_);
v___x_1543_ = lean_nat_dec_lt(v___x_1542_, v_size_1536_);
lean_dec(v___x_1542_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_dec(v_l_1539_);
v___x_1544_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1545_ = lean_nat_add(v___x_1544_, v_size_1536_);
lean_dec(v___x_1544_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 3, v_impl_1533_);
lean_ctor_set(v___x_1054_, 0, v___x_1545_);
v___x_1547_ = v___x_1054_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_impl_1533_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1052_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
else
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1612_; 
lean_inc(v_r_1540_);
lean_inc(v_v_1538_);
lean_inc(v_k_1537_);
lean_inc(v_size_1536_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; lean_object* v_unused_1617_; 
v_unused_1613_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_r_1052_, 2);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_r_1052_, 1);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1617_);
v___x_1550_ = v_r_1052_;
v_isShared_1551_ = v_isSharedCheck_1612_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_r_1052_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1612_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_size_1552_; lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v_l_1555_; lean_object* v_r_1556_; lean_object* v_size_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_size_1552_ = lean_ctor_get(v_l_1539_, 0);
v_k_1553_ = lean_ctor_get(v_l_1539_, 1);
v_v_1554_ = lean_ctor_get(v_l_1539_, 2);
v_l_1555_ = lean_ctor_get(v_l_1539_, 3);
v_r_1556_ = lean_ctor_get(v_l_1539_, 4);
v_size_1557_ = lean_ctor_get(v_r_1540_, 0);
v___x_1558_ = lean_unsigned_to_nat(2u);
v___x_1559_ = lean_nat_mul(v___x_1558_, v_size_1557_);
v___x_1560_ = lean_nat_dec_lt(v_size_1552_, v___x_1559_);
lean_dec(v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1588_; 
lean_inc(v_r_1556_);
lean_inc(v_l_1555_);
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_l_1539_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; 
v_unused_1589_ = lean_ctor_get(v_l_1539_, 4);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1539_, 3);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_l_1539_, 2);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1539_, 1);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1539_, 0);
lean_dec(v_unused_1593_);
v___x_1562_ = v_l_1539_;
v_isShared_1563_ = v_isSharedCheck_1588_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_l_1539_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1588_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1578_; 
v___x_1564_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1565_ = lean_nat_add(v___x_1564_, v_size_1536_);
lean_dec(v_size_1536_);
if (lean_obj_tag(v_l_1555_) == 0)
{
lean_object* v_size_1586_; 
v_size_1586_ = lean_ctor_get(v_l_1555_, 0);
lean_inc(v_size_1586_);
v___y_1578_ = v_size_1586_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_unsigned_to_nat(0u);
v___y_1578_ = v___x_1587_;
goto v___jp_1577_;
}
v___jp_1566_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_nat_add(v___y_1567_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec(v___y_1567_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_r_1540_);
lean_ctor_set(v___x_1562_, 3, v_r_1556_);
lean_ctor_set(v___x_1562_, 2, v_v_1538_);
lean_ctor_set(v___x_1562_, 1, v_k_1537_);
lean_ctor_set(v___x_1562_, 0, v___x_1570_);
v___x_1572_ = v___x_1562_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1576_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1576_, 3, v_r_1556_);
lean_ctor_set(v_reuseFailAlloc_1576_, 4, v_r_1540_);
v___x_1572_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v___x_1572_);
lean_ctor_set(v___x_1550_, 3, v___y_1568_);
lean_ctor_set(v___x_1550_, 2, v_v_1554_);
lean_ctor_set(v___x_1550_, 1, v_k_1553_);
lean_ctor_set(v___x_1550_, 0, v___x_1565_);
v___x_1574_ = v___x_1550_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v___y_1568_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
v___jp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_nat_add(v___x_1564_, v___y_1578_);
lean_dec(v___y_1578_);
lean_dec(v___x_1564_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_l_1555_);
lean_ctor_set(v___x_1054_, 3, v_impl_1533_);
lean_ctor_set(v___x_1054_, 0, v___x_1579_);
v___x_1581_ = v___x_1054_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_impl_1533_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_l_1555_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_nat_add(v___x_1534_, v_size_1557_);
if (lean_obj_tag(v_r_1556_) == 0)
{
lean_object* v_size_1583_; 
v_size_1583_ = lean_ctor_get(v_r_1556_, 0);
lean_inc(v_size_1583_);
v___y_1567_ = v___x_1582_;
v___y_1568_ = v___x_1581_;
v___y_1569_ = v_size_1583_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = lean_unsigned_to_nat(0u);
v___y_1567_ = v___x_1582_;
v___y_1568_ = v___x_1581_;
v___y_1569_ = v___x_1584_;
goto v___jp_1566_;
}
}
}
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_del_object(v___x_1054_);
v___x_1594_ = lean_nat_add(v___x_1534_, v_size_1535_);
v___x_1595_ = lean_nat_add(v___x_1594_, v_size_1536_);
lean_dec(v_size_1536_);
v___x_1596_ = lean_nat_add(v___x_1594_, v_size_1552_);
lean_dec(v___x_1594_);
lean_inc_ref(v_impl_1533_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_l_1539_);
lean_ctor_set(v___x_1550_, 3, v_impl_1533_);
lean_ctor_set(v___x_1550_, 2, v_v_1050_);
lean_ctor_set(v___x_1550_, 1, v_k_1049_);
lean_ctor_set(v___x_1550_, 0, v___x_1596_);
v___x_1598_ = v___x_1550_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_impl_1533_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_l_1539_);
v___x_1598_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
v_isSharedCheck_1605_ = !lean_is_exclusive(v_impl_1533_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_impl_1533_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_impl_1533_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_impl_1533_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_impl_1533_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_impl_1533_, 0);
lean_dec(v_unused_1610_);
v___x_1600_ = v_impl_1533_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_impl_1533_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 4, v_r_1540_);
lean_ctor_set(v___x_1600_, 3, v___x_1598_);
lean_ctor_set(v___x_1600_, 2, v_v_1538_);
lean_ctor_set(v___x_1600_, 1, v_k_1537_);
lean_ctor_set(v___x_1600_, 0, v___x_1595_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1537_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1538_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_r_1540_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
v_size_1618_ = lean_ctor_get(v_impl_1533_, 0);
v___x_1619_ = lean_nat_add(v___x_1534_, v_size_1618_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 3, v_impl_1533_);
lean_ctor_set(v___x_1054_, 0, v___x_1619_);
v___x_1621_ = v___x_1054_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_impl_1533_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v_r_1052_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
if (lean_obj_tag(v_r_1052_) == 0)
{
lean_object* v_l_1623_; 
v_l_1623_ = lean_ctor_get(v_r_1052_, 3);
lean_inc(v_l_1623_);
if (lean_obj_tag(v_l_1623_) == 0)
{
lean_object* v_r_1624_; 
v_r_1624_ = lean_ctor_get(v_r_1052_, 4);
lean_inc(v_r_1624_);
if (lean_obj_tag(v_r_1624_) == 0)
{
lean_object* v_size_1625_; lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1640_; 
v_size_1625_ = lean_ctor_get(v_r_1052_, 0);
v_k_1626_ = lean_ctor_get(v_r_1052_, 1);
v_v_1627_ = lean_ctor_get(v_r_1052_, 2);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; 
v_unused_1641_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1642_);
v___x_1629_ = v_r_1052_;
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_v_1627_);
lean_inc(v_k_1626_);
lean_inc(v_size_1625_);
lean_dec(v_r_1052_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v_size_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v_size_1631_ = lean_ctor_get(v_l_1623_, 0);
v___x_1632_ = lean_nat_add(v___x_1534_, v_size_1625_);
lean_dec(v_size_1625_);
v___x_1633_ = lean_nat_add(v___x_1534_, v_size_1631_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 4, v_l_1623_);
lean_ctor_set(v___x_1629_, 3, v_impl_1533_);
lean_ctor_set(v___x_1629_, 2, v_v_1050_);
lean_ctor_set(v___x_1629_, 1, v_k_1049_);
lean_ctor_set(v___x_1629_, 0, v___x_1633_);
v___x_1635_ = v___x_1629_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_impl_1533_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_l_1623_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_r_1624_);
lean_ctor_set(v___x_1054_, 3, v___x_1635_);
lean_ctor_set(v___x_1054_, 2, v_v_1627_);
lean_ctor_set(v___x_1054_, 1, v_k_1626_);
lean_ctor_set(v___x_1054_, 0, v___x_1632_);
v___x_1637_ = v___x_1054_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v_r_1624_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v_k_1643_; lean_object* v_v_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1667_; 
v_k_1643_ = lean_ctor_get(v_r_1052_, 1);
v_v_1644_ = lean_ctor_get(v_r_1052_, 2);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; 
v_unused_1668_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1670_);
v___x_1646_ = v_r_1052_;
v_isShared_1647_ = v_isSharedCheck_1667_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_v_1644_);
lean_inc(v_k_1643_);
lean_dec(v_r_1052_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1667_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_k_1648_; lean_object* v_v_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1663_; 
v_k_1648_ = lean_ctor_get(v_l_1623_, 1);
v_v_1649_ = lean_ctor_get(v_l_1623_, 2);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_l_1623_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; lean_object* v_unused_1665_; lean_object* v_unused_1666_; 
v_unused_1664_ = lean_ctor_get(v_l_1623_, 4);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_l_1623_, 3);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_l_1623_, 0);
lean_dec(v_unused_1666_);
v___x_1651_ = v_l_1623_;
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_v_1649_);
lean_inc(v_k_1648_);
lean_dec(v_l_1623_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1663_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1655_; 
v___x_1653_ = lean_unsigned_to_nat(3u);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 4, v_r_1624_);
lean_ctor_set(v___x_1651_, 3, v_r_1624_);
lean_ctor_set(v___x_1651_, 2, v_v_1050_);
lean_ctor_set(v___x_1651_, 1, v_k_1049_);
lean_ctor_set(v___x_1651_, 0, v___x_1534_);
v___x_1655_ = v___x_1651_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1662_, 3, v_r_1624_);
lean_ctor_set(v_reuseFailAlloc_1662_, 4, v_r_1624_);
v___x_1655_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1657_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 3, v_r_1624_);
lean_ctor_set(v___x_1646_, 0, v___x_1534_);
v___x_1657_ = v___x_1646_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1643_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1644_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_r_1624_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_r_1624_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1657_);
lean_ctor_set(v___x_1054_, 3, v___x_1655_);
lean_ctor_set(v___x_1054_, 2, v_v_1649_);
lean_ctor_set(v___x_1054_, 1, v_k_1648_);
lean_ctor_set(v___x_1054_, 0, v___x_1653_);
v___x_1659_ = v___x_1054_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1648_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1649_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1671_; 
v_r_1671_ = lean_ctor_get(v_r_1052_, 4);
lean_inc(v_r_1671_);
if (lean_obj_tag(v_r_1671_) == 0)
{
lean_object* v_k_1672_; lean_object* v_v_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1684_; 
v_k_1672_ = lean_ctor_get(v_r_1052_, 1);
v_v_1673_ = lean_ctor_get(v_r_1052_, 2);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1685_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_r_1052_, 0);
lean_dec(v_unused_1687_);
v___x_1675_ = v_r_1052_;
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_v_1673_);
lean_inc(v_k_1672_);
lean_dec(v_r_1052_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1684_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_unsigned_to_nat(3u);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 4, v_l_1623_);
lean_ctor_set(v___x_1675_, 2, v_v_1050_);
lean_ctor_set(v___x_1675_, 1, v_k_1049_);
lean_ctor_set(v___x_1675_, 0, v___x_1534_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_l_1623_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_l_1623_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v_r_1671_);
lean_ctor_set(v___x_1054_, 3, v___x_1679_);
lean_ctor_set(v___x_1054_, 2, v_v_1673_);
lean_ctor_set(v___x_1054_, 1, v_k_1672_);
lean_ctor_set(v___x_1054_, 0, v___x_1677_);
v___x_1681_ = v___x_1054_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1672_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1673_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_r_1671_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_size_1688_; lean_object* v_k_1689_; lean_object* v_v_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1701_; 
v_size_1688_ = lean_ctor_get(v_r_1052_, 0);
v_k_1689_ = lean_ctor_get(v_r_1052_, 1);
v_v_1690_ = lean_ctor_get(v_r_1052_, 2);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; 
v_unused_1702_ = lean_ctor_get(v_r_1052_, 4);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_r_1052_, 3);
lean_dec(v_unused_1703_);
v___x_1692_ = v_r_1052_;
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_v_1690_);
lean_inc(v_k_1689_);
lean_inc(v_size_1688_);
lean_dec(v_r_1052_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1701_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 3, v_r_1671_);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_size_1688_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1689_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1690_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_r_1671_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v_r_1671_);
v___x_1695_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_unsigned_to_nat(2u);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1695_);
lean_ctor_set(v___x_1054_, 3, v_r_1671_);
lean_ctor_set(v___x_1054_, 0, v___x_1696_);
v___x_1698_ = v___x_1054_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_r_1671_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v___x_1695_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
else
{
lean_object* v___x_1705_; 
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 3, v_r_1052_);
lean_ctor_set(v___x_1054_, 0, v___x_1534_);
v___x_1705_ = v___x_1054_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1534_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v_k_1049_);
lean_ctor_set(v_reuseFailAlloc_1706_, 2, v_v_1050_);
lean_ctor_set(v_reuseFailAlloc_1706_, 3, v_r_1052_);
lean_ctor_set(v_reuseFailAlloc_1706_, 4, v_r_1052_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
}
else
{
return v_t_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg___boxed(lean_object* v_k_1709_, lean_object* v_t_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(v_k_1709_, v_t_1710_);
lean_dec(v_k_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__2(lean_object* v_init_1712_, lean_object* v_x_1713_){
_start:
{
if (lean_obj_tag(v_x_1713_) == 0)
{
lean_object* v_v_1714_; lean_object* v_l_1715_; lean_object* v_r_1716_; lean_object* v___x_1717_; lean_object* v_ordered_1718_; lean_object* v_index_1719_; lean_object* v_lin_1720_; lean_object* v_k_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v_i_1725_; lean_object* v___x_1726_; 
v_v_1714_ = lean_ctor_get(v_x_1713_, 2);
lean_inc(v_v_1714_);
v_l_1715_ = lean_ctor_get(v_x_1713_, 3);
lean_inc(v_l_1715_);
v_r_1716_ = lean_ctor_get(v_x_1713_, 4);
lean_inc(v_r_1716_);
lean_dec_ref_known(v_x_1713_, 5);
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__2(v_init_1712_, v_r_1716_);
v_ordered_1718_ = lean_ctor_get(v___x_1717_, 0);
v_index_1719_ = lean_ctor_get(v___x_1717_, 1);
v_lin_1720_ = lean_ctor_get(v_v_1714_, 0);
v_k_1721_ = lean_ctor_get(v_v_1714_, 1);
v___x_1722_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0, &l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3___closed__0);
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_ordered_1718_, v___x_1722_);
v___x_1724_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__0);
v_i_1725_ = lean_int_sub(v___x_1723_, v___x_1724_);
lean_dec(v___x_1723_);
lean_inc_ref(v___x_1717_);
v___x_1726_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(v___x_1717_, v_lin_1720_);
if (lean_obj_tag(v___x_1726_) == 1)
{
lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1743_; 
lean_inc_ref(v_index_1719_);
lean_inc(v_ordered_1718_);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; lean_object* v_unused_1745_; 
v_unused_1744_ = lean_ctor_get(v___x_1717_, 1);
lean_dec(v_unused_1744_);
v_unused_1745_ = lean_ctor_get(v___x_1717_, 0);
lean_dec(v_unused_1745_);
v___x_1728_ = v___x_1717_;
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v___x_1717_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_val_1730_; lean_object* v_snd_1731_; lean_object* v_fst_1732_; lean_object* v_k_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v_val_1730_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v___x_1726_, 1);
v_snd_1731_ = lean_ctor_get(v_val_1730_, 1);
lean_inc(v_snd_1731_);
v_fst_1732_ = lean_ctor_get(v_val_1730_, 0);
lean_inc(v_fst_1732_);
lean_dec(v_val_1730_);
v_k_1733_ = lean_ctor_get(v_snd_1731_, 1);
v___x_1734_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(v_fst_1732_, v_ordered_1718_);
lean_dec(v_fst_1732_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 0, v___x_1734_);
v___x_1736_ = v___x_1728_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_index_1719_);
v___x_1736_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_int_dec_lt(v_k_1721_, v_k_1733_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; 
lean_dec(v_snd_1731_);
v___x_1738_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v___x_1736_, v_i_1725_, v_v_1714_);
v_init_1712_ = v___x_1738_;
v_x_1713_ = v_l_1715_;
goto _start;
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_v_1714_);
v___x_1740_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v___x_1736_, v_i_1725_, v_snd_1731_);
v_init_1712_ = v___x_1740_;
v_x_1713_ = v_l_1715_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1746_; 
lean_dec(v___x_1726_);
v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v___x_1717_, v_i_1725_, v_v_1714_);
v_init_1712_ = v___x_1746_;
v_x_1713_ = v_l_1715_;
goto _start;
}
}
else
{
return v_init_1712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds(lean_object* v_as_1748_, lean_object* v_bs_1749_){
_start:
{
lean_object* v_ordered_1750_; 
v_ordered_1750_ = lean_ctor_get(v_as_1748_, 0);
if (lean_obj_tag(v_ordered_1750_) == 0)
{
lean_object* v_ordered_1751_; 
v_ordered_1751_ = lean_ctor_get(v_bs_1749_, 0);
if (lean_obj_tag(v_ordered_1751_) == 0)
{
lean_object* v_size_1752_; lean_object* v_size_1753_; uint8_t v___x_1754_; 
v_size_1752_ = lean_ctor_get(v_ordered_1750_, 0);
v_size_1753_ = lean_ctor_get(v_ordered_1751_, 0);
v___x_1754_ = lean_nat_dec_le(v_size_1753_, v_size_1752_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_inc_ref(v_ordered_1750_);
lean_dec_ref(v_as_1748_);
v___x_1755_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__2(v_bs_1749_, v_ordered_1750_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
lean_inc_ref(v_ordered_1751_);
lean_dec_ref(v_bs_1749_);
v___x_1756_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3(v_as_1748_, v_ordered_1751_);
return v___x_1756_;
}
}
else
{
lean_dec_ref(v_bs_1749_);
return v_as_1748_;
}
}
else
{
lean_dec_ref(v_as_1748_);
return v_bs_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0(lean_object* v_00_u03b2_1757_, lean_object* v_k_1758_, lean_object* v_t_1759_, lean_object* v_h_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___redArg(v_k_1758_, v_t_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_k_1763_, lean_object* v_t_1764_, lean_object* v_h_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__0(v_00_u03b2_1762_, v_k_1763_, v_t_1764_, v_h_1765_);
lean_dec(v_k_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3(lean_object* v_init_1767_, lean_object* v_t_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_andBounds_spec__3_spec__3(v_init_1767_, v_t_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0(lean_object* v_snd_1770_, lean_object* v_bs_1771_, lean_object* v_as_1772_, lean_object* v_init_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_object* v_k_1775_; lean_object* v_v_1776_; lean_object* v_l_1777_; lean_object* v_r_1778_; lean_object* v___x_1779_; lean_object* v_a_1780_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v_lin_1786_; lean_object* v_k_1787_; lean_object* v___x_1788_; 
v_k_1775_ = lean_ctor_get(v_x_1774_, 1);
lean_inc(v_k_1775_);
v_v_1776_ = lean_ctor_get(v_x_1774_, 2);
lean_inc(v_v_1776_);
v_l_1777_ = lean_ctor_get(v_x_1774_, 3);
lean_inc(v_l_1777_);
v_r_1778_ = lean_ctor_get(v_x_1774_, 4);
lean_inc(v_r_1778_);
lean_dec_ref_known(v_x_1774_, 5);
lean_inc_ref_n(v_snd_1770_, 2);
v___x_1779_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0(v_snd_1770_, v_bs_1771_, v_as_1772_, v_init_1773_, v_l_1777_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v_lin_1786_ = lean_ctor_get(v_v_1776_, 0);
v_k_1787_ = lean_ctor_get(v_v_1776_, 1);
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(v_snd_1770_, v_lin_1786_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___y_1793_; lean_object* v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1801_; lean_object* v_ordered_1805_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v_fst_1790_ = lean_ctor_get(v_val_1789_, 0);
lean_inc(v_fst_1790_);
v_snd_1791_ = lean_ctor_get(v_val_1789_, 1);
lean_inc(v_snd_1791_);
lean_dec(v_val_1789_);
v_ordered_1805_ = lean_ctor_get(v_as_1772_, 0);
if (lean_obj_tag(v_ordered_1805_) == 0)
{
lean_object* v_size_1806_; 
v_size_1806_ = lean_ctor_get(v_ordered_1805_, 0);
v___y_1801_ = v_size_1806_;
goto v___jp_1800_;
}
else
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___y_1801_ = v___x_1807_;
goto v___jp_1800_;
}
v___jp_1792_:
{
lean_object* v_k_1794_; uint8_t v___x_1795_; 
v_k_1794_ = lean_ctor_get(v_snd_1791_, 1);
v___x_1795_ = lean_int_dec_le(v_k_1787_, v_k_1794_);
if (v___x_1795_ == 0)
{
lean_dec(v_v_1776_);
v___y_1782_ = v___y_1793_;
v___y_1783_ = v_snd_1791_;
goto v___jp_1781_;
}
else
{
lean_dec(v_snd_1791_);
v___y_1782_ = v___y_1793_;
v___y_1783_ = v_v_1776_;
goto v___jp_1781_;
}
}
v___jp_1796_:
{
uint8_t v___x_1799_; 
v___x_1799_ = lean_nat_dec_le(v___y_1797_, v___y_1798_);
if (v___x_1799_ == 0)
{
lean_dec(v_k_1775_);
v___y_1793_ = v_fst_1790_;
goto v___jp_1792_;
}
else
{
lean_dec(v_fst_1790_);
v___y_1793_ = v_k_1775_;
goto v___jp_1792_;
}
}
v___jp_1800_:
{
lean_object* v_ordered_1802_; 
v_ordered_1802_ = lean_ctor_get(v_bs_1771_, 0);
if (lean_obj_tag(v_ordered_1802_) == 0)
{
lean_object* v_size_1803_; 
v_size_1803_ = lean_ctor_get(v_ordered_1802_, 0);
v___y_1797_ = v___y_1801_;
v___y_1798_ = v_size_1803_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_unsigned_to_nat(0u);
v___y_1797_ = v___y_1801_;
v___y_1798_ = v___x_1804_;
goto v___jp_1796_;
}
}
}
else
{
lean_dec(v___x_1788_);
lean_dec(v_v_1776_);
lean_dec(v_k_1775_);
v_init_1773_ = v_a_1780_;
v_x_1774_ = v_r_1778_;
goto _start;
}
v___jp_1781_:
{
lean_object* v___x_1784_; 
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_insertAt(v_a_1780_, v___y_1782_, v___y_1783_);
v_init_1773_ = v___x_1784_;
v_x_1774_ = v_r_1778_;
goto _start;
}
}
else
{
lean_object* v___x_1809_; 
lean_dec_ref(v_snd_1770_);
v___x_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1809_, 0, v_init_1773_);
return v___x_1809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0___boxed(lean_object* v_snd_1810_, lean_object* v_bs_1811_, lean_object* v_as_1812_, lean_object* v_init_1813_, lean_object* v_x_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0(v_snd_1810_, v_bs_1811_, v_as_1812_, v_init_1813_, v_x_1814_);
lean_dec_ref(v_as_1812_);
lean_dec_ref(v_bs_1811_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds(lean_object* v_as_1816_, lean_object* v_bs_1817_){
_start:
{
lean_object* v_ordered_1819_; lean_object* v_snd_1820_; lean_object* v_ordered_1824_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1831_; 
v_ordered_1824_ = lean_ctor_get(v_as_1816_, 0);
if (lean_obj_tag(v_ordered_1824_) == 0)
{
lean_object* v_size_1835_; 
v_size_1835_ = lean_ctor_get(v_ordered_1824_, 0);
lean_inc(v_size_1835_);
v___y_1831_ = v_size_1835_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___y_1831_ = v___x_1836_;
goto v___jp_1830_;
}
v___jp_1818_:
{
lean_object* v_result_1821_; lean_object* v___x_1822_; lean_object* v_a_1823_; 
v_result_1821_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_orBounds_spec__0(v_snd_1820_, v_bs_1817_, v_as_1816_, v_result_1821_, v_ordered_1819_);
lean_dec_ref(v_as_1816_);
lean_dec_ref(v_bs_1817_);
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
return v_a_1823_;
}
v___jp_1825_:
{
uint8_t v___x_1828_; 
v___x_1828_ = lean_nat_dec_le(v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec(v___y_1826_);
if (v___x_1828_ == 0)
{
lean_object* v_ordered_1829_; 
v_ordered_1829_ = lean_ctor_get(v_bs_1817_, 0);
lean_inc_ref(v_as_1816_);
lean_inc(v_ordered_1829_);
v_ordered_1819_ = v_ordered_1829_;
v_snd_1820_ = v_as_1816_;
goto v___jp_1818_;
}
else
{
lean_inc_ref(v_bs_1817_);
lean_inc(v_ordered_1824_);
v_ordered_1819_ = v_ordered_1824_;
v_snd_1820_ = v_bs_1817_;
goto v___jp_1818_;
}
}
v___jp_1830_:
{
lean_object* v_ordered_1832_; 
v_ordered_1832_ = lean_ctor_get(v_bs_1817_, 0);
if (lean_obj_tag(v_ordered_1832_) == 0)
{
lean_object* v_size_1833_; 
v_size_1833_ = lean_ctor_get(v_ordered_1832_, 0);
lean_inc(v_size_1833_);
v___y_1826_ = v___y_1831_;
v___y_1827_ = v_size_1833_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___y_1826_ = v___y_1831_;
v___y_1827_ = v___x_1834_;
goto v___jp_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg(lean_object* v_a_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_box(0);
return v___x_1839_;
}
else
{
lean_object* v_key_1840_; lean_object* v_value_1841_; lean_object* v_tail_1842_; size_t v___x_1843_; size_t v___x_1844_; uint8_t v___x_1845_; 
v_key_1840_ = lean_ctor_get(v_x_1838_, 0);
v_value_1841_ = lean_ctor_get(v_x_1838_, 1);
v_tail_1842_ = lean_ctor_get(v_x_1838_, 2);
v___x_1843_ = lean_ptr_addr(v_key_1840_);
v___x_1844_ = lean_ptr_addr(v_a_1837_);
v___x_1845_ = lean_usize_dec_eq(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
v_x_1838_ = v_tail_1842_;
goto _start;
}
else
{
lean_object* v___x_1847_; 
lean_inc(v_value_1841_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_value_1841_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg___boxed(lean_object* v_a_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg(v_a_1848_, v_x_1849_);
lean_dec(v_x_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1852_) == 0)
{
return v_x_1851_;
}
else
{
lean_object* v_key_1853_; lean_object* v_value_1854_; lean_object* v_tail_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1881_; 
v_key_1853_ = lean_ctor_get(v_x_1852_, 0);
v_value_1854_ = lean_ctor_get(v_x_1852_, 1);
v_tail_1855_ = lean_ctor_get(v_x_1852_, 2);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1852_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1857_ = v_x_1852_;
v_isShared_1858_ = v_isSharedCheck_1881_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_tail_1855_);
lean_inc(v_value_1854_);
lean_inc(v_key_1853_);
lean_dec(v_x_1852_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1881_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; uint64_t v___x_1863_; uint64_t v___x_1864_; uint64_t v___x_1865_; uint64_t v_fold_1866_; uint64_t v___x_1867_; uint64_t v___x_1868_; uint64_t v___x_1869_; size_t v___x_1870_; size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1859_ = lean_array_get_size(v_x_1851_);
v___x_1860_ = lean_ptr_addr(v_key_1853_);
v___x_1861_ = ((size_t)3ULL);
v___x_1862_ = lean_usize_shift_right(v___x_1860_, v___x_1861_);
v___x_1863_ = lean_usize_to_uint64(v___x_1862_);
v___x_1864_ = 32ULL;
v___x_1865_ = lean_uint64_shift_right(v___x_1863_, v___x_1864_);
v_fold_1866_ = lean_uint64_xor(v___x_1863_, v___x_1865_);
v___x_1867_ = 16ULL;
v___x_1868_ = lean_uint64_shift_right(v_fold_1866_, v___x_1867_);
v___x_1869_ = lean_uint64_xor(v_fold_1866_, v___x_1868_);
v___x_1870_ = lean_uint64_to_usize(v___x_1869_);
v___x_1871_ = lean_usize_of_nat(v___x_1859_);
v___x_1872_ = ((size_t)1ULL);
v___x_1873_ = lean_usize_sub(v___x_1871_, v___x_1872_);
v___x_1874_ = lean_usize_land(v___x_1870_, v___x_1873_);
v___x_1875_ = lean_array_uget_borrowed(v_x_1851_, v___x_1874_);
lean_inc(v___x_1875_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 2, v___x_1875_);
v___x_1877_ = v___x_1857_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_key_1853_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_value_1854_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_array_uset(v_x_1851_, v___x_1874_, v___x_1877_);
v_x_1851_ = v___x_1878_;
v_x_1852_ = v_tail_1855_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1___redArg(lean_object* v_i_1882_, lean_object* v_source_1883_, lean_object* v_target_1884_){
_start:
{
lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1885_ = lean_array_get_size(v_source_1883_);
v___x_1886_ = lean_nat_dec_lt(v_i_1882_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_dec_ref(v_source_1883_);
lean_dec(v_i_1882_);
return v_target_1884_;
}
else
{
lean_object* v_es_1887_; lean_object* v___x_1888_; lean_object* v_source_1889_; lean_object* v_target_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_es_1887_ = lean_array_fget(v_source_1883_, v_i_1882_);
v___x_1888_ = lean_box(0);
v_source_1889_ = lean_array_fset(v_source_1883_, v_i_1882_, v___x_1888_);
v_target_1890_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2___redArg(v_target_1884_, v_es_1887_);
v___x_1891_ = lean_unsigned_to_nat(1u);
v___x_1892_ = lean_nat_add(v_i_1882_, v___x_1891_);
lean_dec(v_i_1882_);
v_i_1882_ = v___x_1892_;
v_source_1883_ = v_source_1889_;
v_target_1884_ = v_target_1890_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1___redArg(lean_object* v_data_1894_){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_nbuckets_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1895_ = lean_array_get_size(v_data_1894_);
v___x_1896_ = lean_unsigned_to_nat(2u);
v_nbuckets_1897_ = lean_nat_mul(v___x_1895_, v___x_1896_);
v___x_1898_ = lean_unsigned_to_nat(0u);
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_mk_array(v_nbuckets_1897_, v___x_1899_);
v___x_1901_ = lean_array_propagate_mark(v_data_1894_, v___x_1900_);
v___x_1902_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1___redArg(v___x_1898_, v_data_1894_, v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg(lean_object* v_e_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_Sym_shareCommon(v_e_1903_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1978_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1978_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1978_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v_vars_1918_; lean_object* v_directions_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1977_; 
v___x_1917_ = lean_st_ref_take(v_a_1904_);
v_vars_1918_ = lean_ctor_get(v___x_1917_, 0);
v_directions_1919_ = lean_ctor_get(v___x_1917_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1921_ = v___x_1917_;
v_isShared_1922_ = v_isSharedCheck_1977_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_directions_1919_);
lean_inc(v_vars_1918_);
lean_dec(v___x_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1977_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_size_1933_; lean_object* v_buckets_1934_; lean_object* v___x_1935_; size_t v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v___x_1941_; uint64_t v_fold_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; uint64_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; lean_object* v_bkt_1951_; lean_object* v___x_1952_; 
v_size_1933_ = lean_ctor_get(v_vars_1918_, 0);
v_buckets_1934_ = lean_ctor_get(v_vars_1918_, 1);
v___x_1935_ = lean_array_get_size(v_buckets_1934_);
v___x_1936_ = lean_ptr_addr(v_a_1913_);
v___x_1937_ = ((size_t)3ULL);
v___x_1938_ = lean_usize_shift_right(v___x_1936_, v___x_1937_);
v___x_1939_ = lean_usize_to_uint64(v___x_1938_);
v___x_1940_ = 32ULL;
v___x_1941_ = lean_uint64_shift_right(v___x_1939_, v___x_1940_);
v_fold_1942_ = lean_uint64_xor(v___x_1939_, v___x_1941_);
v___x_1943_ = 16ULL;
v___x_1944_ = lean_uint64_shift_right(v_fold_1942_, v___x_1943_);
v___x_1945_ = lean_uint64_xor(v_fold_1942_, v___x_1944_);
v___x_1946_ = lean_uint64_to_usize(v___x_1945_);
v___x_1947_ = lean_usize_of_nat(v___x_1935_);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_sub(v___x_1947_, v___x_1948_);
v___x_1950_ = lean_usize_land(v___x_1946_, v___x_1949_);
v_bkt_1951_ = lean_array_uget_borrowed(v_buckets_1934_, v___x_1950_);
v___x_1952_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg(v_a_1913_, v_bkt_1951_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1973_; 
lean_inc_ref(v_buckets_1934_);
lean_inc(v_size_1933_);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_vars_1918_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; lean_object* v_unused_1975_; 
v_unused_1974_ = lean_ctor_get(v_vars_1918_, 1);
lean_dec(v_unused_1974_);
v_unused_1975_ = lean_ctor_get(v_vars_1918_, 0);
lean_dec(v_unused_1975_);
v___x_1954_ = v_vars_1918_;
v_isShared_1955_ = v_isSharedCheck_1973_;
goto v_resetjp_1953_;
}
else
{
lean_dec(v_vars_1918_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1973_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v_size_x27_1957_; lean_object* v___x_1958_; lean_object* v_buckets_x27_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v_size_x27_1957_ = lean_nat_add(v_size_1933_, v___x_1956_);
lean_inc(v_bkt_1951_);
lean_inc(v_size_1933_);
v___x_1958_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1913_);
lean_ctor_set(v___x_1958_, 1, v_size_1933_);
lean_ctor_set(v___x_1958_, 2, v_bkt_1951_);
v_buckets_x27_1959_ = lean_array_uset(v_buckets_1934_, v___x_1950_, v___x_1958_);
v___x_1960_ = lean_unsigned_to_nat(4u);
v___x_1961_ = lean_nat_mul(v_size_x27_1957_, v___x_1960_);
v___x_1962_ = lean_unsigned_to_nat(3u);
v___x_1963_ = lean_nat_div(v___x_1961_, v___x_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_array_get_size(v_buckets_x27_1959_);
v___x_1965_ = lean_nat_dec_le(v___x_1963_, v___x_1964_);
lean_dec(v___x_1963_);
if (v___x_1965_ == 0)
{
lean_object* v_val_1966_; lean_object* v___x_1968_; 
v_val_1966_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1___redArg(v_buckets_x27_1959_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_val_1966_);
lean_ctor_set(v___x_1954_, 0, v_size_x27_1957_);
v___x_1968_ = v___x_1954_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_size_x27_1957_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_val_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v___y_1924_ = v___x_1968_;
v___y_1925_ = v_size_1933_;
goto v___jp_1923_;
}
}
else
{
lean_object* v___x_1971_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_buckets_x27_1959_);
lean_ctor_set(v___x_1954_, 0, v_size_x27_1957_);
v___x_1971_ = v___x_1954_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_size_x27_1957_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_buckets_x27_1959_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v___y_1924_ = v___x_1971_;
v___y_1925_ = v_size_1933_;
goto v___jp_1923_;
}
}
}
}
else
{
lean_object* v_val_1976_; 
lean_dec(v_a_1913_);
v_val_1976_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_val_1976_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1924_ = v_vars_1918_;
v___y_1925_ = v_val_1976_;
goto v___jp_1923_;
}
v___jp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___y_1924_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___y_1924_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_directions_1919_);
v___x_1927_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = lean_st_ref_put(v_a_1904_, v___x_1927_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___y_1925_);
v___x_1930_ = v___x_1915_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___y_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
v_a_1979_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1912_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1912_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg___boxed(lean_object* v_e_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg(v_e_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar(lean_object* v_e_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg(v_e_1997_, v_a_1998_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___boxed(lean_object* v_e_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar(v_e_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec_ref(v_a_2017_);
lean_dec(v_a_2016_);
lean_dec_ref(v_a_2015_);
lean_dec(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec(v_a_2012_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0(lean_object* v_00_u03b2_2025_, lean_object* v_a_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___redArg(v_a_2026_, v_x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0___boxed(lean_object* v_00_u03b2_2029_, lean_object* v_a_2030_, lean_object* v_x_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__0(v_00_u03b2_2029_, v_a_2030_, v_x_2031_);
lean_dec(v_x_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1(lean_object* v_00_u03b2_2033_, lean_object* v_data_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1___redArg(v_data_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1(lean_object* v_00_u03b2_2036_, lean_object* v_i_2037_, lean_object* v_source_2038_, lean_object* v_target_2039_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1___redArg(v_i_2037_, v_source_2038_, v_target_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar_spec__1_spec__1_spec__2___redArg(v_x_2042_, v_x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2___redArg(lean_object* v_x_2045_, lean_object* v_x_2046_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
return v_x_2045_;
}
else
{
lean_object* v_key_2047_; lean_object* v_value_2048_; lean_object* v_tail_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2072_; 
v_key_2047_ = lean_ctor_get(v_x_2046_, 0);
v_value_2048_ = lean_ctor_get(v_x_2046_, 1);
v_tail_2049_ = lean_ctor_get(v_x_2046_, 2);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_x_2046_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2051_ = v_x_2046_;
v_isShared_2052_ = v_isSharedCheck_2072_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_tail_2049_);
lean_inc(v_value_2048_);
lean_inc(v_key_2047_);
lean_dec(v_x_2046_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2072_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; uint64_t v___x_2056_; uint64_t v_fold_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; uint64_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2053_ = lean_array_get_size(v_x_2045_);
v___x_2054_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_key_2047_);
v___x_2055_ = 32ULL;
v___x_2056_ = lean_uint64_shift_right(v___x_2054_, v___x_2055_);
v_fold_2057_ = lean_uint64_xor(v___x_2054_, v___x_2056_);
v___x_2058_ = 16ULL;
v___x_2059_ = lean_uint64_shift_right(v_fold_2057_, v___x_2058_);
v___x_2060_ = lean_uint64_xor(v_fold_2057_, v___x_2059_);
v___x_2061_ = lean_uint64_to_usize(v___x_2060_);
v___x_2062_ = lean_usize_of_nat(v___x_2053_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_sub(v___x_2062_, v___x_2063_);
v___x_2065_ = lean_usize_land(v___x_2061_, v___x_2064_);
v___x_2066_ = lean_array_uget_borrowed(v_x_2045_, v___x_2065_);
lean_inc(v___x_2066_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 2, v___x_2066_);
v___x_2068_ = v___x_2051_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_key_2047_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_value_2048_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_array_uset(v_x_2045_, v___x_2065_, v___x_2068_);
v_x_2045_ = v___x_2069_;
v_x_2046_ = v_tail_2049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1___redArg(lean_object* v_i_2073_, lean_object* v_source_2074_, lean_object* v_target_2075_){
_start:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_array_get_size(v_source_2074_);
v___x_2077_ = lean_nat_dec_lt(v_i_2073_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_dec_ref(v_source_2074_);
lean_dec(v_i_2073_);
return v_target_2075_;
}
else
{
lean_object* v_es_2078_; lean_object* v___x_2079_; lean_object* v_source_2080_; lean_object* v_target_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_es_2078_ = lean_array_fget(v_source_2074_, v_i_2073_);
v___x_2079_ = lean_box(0);
v_source_2080_ = lean_array_fset(v_source_2074_, v_i_2073_, v___x_2079_);
v_target_2081_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2___redArg(v_target_2075_, v_es_2078_);
v___x_2082_ = lean_unsigned_to_nat(1u);
v___x_2083_ = lean_nat_add(v_i_2073_, v___x_2082_);
lean_dec(v_i_2073_);
v_i_2073_ = v___x_2083_;
v_source_2074_ = v_source_2080_;
v_target_2075_ = v_target_2081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1___redArg(lean_object* v_data_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_nbuckets_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2086_ = lean_array_get_size(v_data_2085_);
v___x_2087_ = lean_unsigned_to_nat(2u);
v_nbuckets_2088_ = lean_nat_mul(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_box(0);
v___x_2091_ = lean_mk_array(v_nbuckets_2088_, v___x_2090_);
v___x_2092_ = lean_array_propagate_mark(v_data_2085_, v___x_2091_);
v___x_2093_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1___redArg(v___x_2089_, v_data_2085_, v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg(lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2095_) == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_box(0);
return v___x_2096_;
}
else
{
lean_object* v_key_2097_; lean_object* v_value_2098_; lean_object* v_tail_2099_; uint8_t v___x_2100_; 
v_key_2097_ = lean_ctor_get(v_x_2095_, 0);
v_value_2098_ = lean_ctor_get(v_x_2095_, 1);
v_tail_2099_ = lean_ctor_get(v_x_2095_, 2);
v___x_2100_ = l_Int_Internal_Linear_instBEqPoly_beq(v_key_2097_, v_a_2094_);
if (v___x_2100_ == 0)
{
v_x_2095_ = v_tail_2099_;
goto _start;
}
else
{
lean_object* v___x_2102_; 
lean_inc(v_value_2098_);
v___x_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2102_, 0, v_value_2098_);
return v___x_2102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg___boxed(lean_object* v_a_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg(v_a_2103_, v_x_2104_);
lean_dec(v_x_2104_);
lean_dec_ref(v_a_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(lean_object* v_lin_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v_vars_2110_; lean_object* v_directions_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2164_; 
v___x_2109_ = lean_st_ref_take(v_a_2107_);
v_vars_2110_ = lean_ctor_get(v___x_2109_, 0);
v_directions_2111_ = lean_ctor_get(v___x_2109_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2113_ = v___x_2109_;
v_isShared_2114_ = v_isSharedCheck_2164_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_directions_2111_);
lean_inc(v_vars_2110_);
lean_dec(v___x_2109_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2164_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v_size_2123_; lean_object* v_buckets_2124_; lean_object* v___x_2125_; uint64_t v___x_2126_; uint64_t v___x_2127_; uint64_t v___x_2128_; uint64_t v_fold_2129_; uint64_t v___x_2130_; uint64_t v___x_2131_; uint64_t v___x_2132_; size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; size_t v___x_2137_; lean_object* v_bkt_2138_; lean_object* v___x_2139_; 
v_size_2123_ = lean_ctor_get(v_directions_2111_, 0);
v_buckets_2124_ = lean_ctor_get(v_directions_2111_, 1);
v___x_2125_ = lean_array_get_size(v_buckets_2124_);
v___x_2126_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_lin_2106_);
v___x_2127_ = 32ULL;
v___x_2128_ = lean_uint64_shift_right(v___x_2126_, v___x_2127_);
v_fold_2129_ = lean_uint64_xor(v___x_2126_, v___x_2128_);
v___x_2130_ = 16ULL;
v___x_2131_ = lean_uint64_shift_right(v_fold_2129_, v___x_2130_);
v___x_2132_ = lean_uint64_xor(v_fold_2129_, v___x_2131_);
v___x_2133_ = lean_uint64_to_usize(v___x_2132_);
v___x_2134_ = lean_usize_of_nat(v___x_2125_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_sub(v___x_2134_, v___x_2135_);
v___x_2137_ = lean_usize_land(v___x_2133_, v___x_2136_);
v_bkt_2138_ = lean_array_uget_borrowed(v_buckets_2124_, v___x_2137_);
v___x_2139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg(v_lin_2106_, v_bkt_2138_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2160_; 
lean_inc_ref(v_buckets_2124_);
lean_inc(v_size_2123_);
v_isSharedCheck_2160_ = !lean_is_exclusive(v_directions_2111_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; 
v_unused_2161_ = lean_ctor_get(v_directions_2111_, 1);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_directions_2111_, 0);
lean_dec(v_unused_2162_);
v___x_2141_ = v_directions_2111_;
v_isShared_2142_ = v_isSharedCheck_2160_;
goto v_resetjp_2140_;
}
else
{
lean_dec(v_directions_2111_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2160_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v_size_x27_2144_; lean_object* v___x_2145_; lean_object* v_buckets_x27_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v_size_x27_2144_ = lean_nat_add(v_size_2123_, v___x_2143_);
lean_inc(v_bkt_2138_);
lean_inc(v_size_2123_);
v___x_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2145_, 0, v_lin_2106_);
lean_ctor_set(v___x_2145_, 1, v_size_2123_);
lean_ctor_set(v___x_2145_, 2, v_bkt_2138_);
v_buckets_x27_2146_ = lean_array_uset(v_buckets_2124_, v___x_2137_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(4u);
v___x_2148_ = lean_nat_mul(v_size_x27_2144_, v___x_2147_);
v___x_2149_ = lean_unsigned_to_nat(3u);
v___x_2150_ = lean_nat_div(v___x_2148_, v___x_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_array_get_size(v_buckets_x27_2146_);
v___x_2152_ = lean_nat_dec_le(v___x_2150_, v___x_2151_);
lean_dec(v___x_2150_);
if (v___x_2152_ == 0)
{
lean_object* v_val_2153_; lean_object* v___x_2155_; 
v_val_2153_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1___redArg(v_buckets_x27_2146_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v_val_2153_);
lean_ctor_set(v___x_2141_, 0, v_size_x27_2144_);
v___x_2155_ = v___x_2141_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_size_x27_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_val_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
v___y_2116_ = v___x_2155_;
v___y_2117_ = v_size_2123_;
goto v___jp_2115_;
}
}
else
{
lean_object* v___x_2158_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v_buckets_x27_2146_);
lean_ctor_set(v___x_2141_, 0, v_size_x27_2144_);
v___x_2158_ = v___x_2141_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_size_x27_2144_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_buckets_x27_2146_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v___y_2116_ = v___x_2158_;
v___y_2117_ = v_size_2123_;
goto v___jp_2115_;
}
}
}
}
else
{
lean_object* v_val_2163_; 
lean_dec_ref(v_lin_2106_);
v_val_2163_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_val_2163_);
lean_dec_ref_known(v___x_2139_, 1);
v___y_2116_ = v_directions_2111_;
v___y_2117_ = v_val_2163_;
goto v___jp_2115_;
}
v___jp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 1, v___y_2116_);
v___x_2119_ = v___x_2113_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_vars_2110_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v___y_2116_);
v___x_2119_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = lean_st_ref_put(v_a_2107_, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___y_2117_);
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg___boxed(lean_object* v_lin_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(v_lin_2165_, v_a_2166_);
lean_dec(v_a_2166_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection(lean_object* v_lin_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(v_lin_2169_, v_a_2170_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___boxed(lean_object* v_lin_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection(v_lin_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec(v_a_2184_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0(lean_object* v_00_u03b2_2197_, lean_object* v_a_2198_, lean_object* v_x_2199_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___redArg(v_a_2198_, v_x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0___boxed(lean_object* v_00_u03b2_2201_, lean_object* v_a_2202_, lean_object* v_x_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__0(v_00_u03b2_2201_, v_a_2202_, v_x_2203_);
lean_dec(v_x_2203_);
lean_dec_ref(v_a_2202_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1(lean_object* v_00_u03b2_2205_, lean_object* v_data_2206_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1___redArg(v_data_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1(lean_object* v_00_u03b2_2208_, lean_object* v_i_2209_, lean_object* v_source_2210_, lean_object* v_target_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1___redArg(v_i_2209_, v_source_2210_, v_target_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection_spec__1_spec__1_spec__2___redArg(v_x_2214_, v_x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(lean_object* v_k_2217_, lean_object* v_t_2218_){
_start:
{
if (lean_obj_tag(v_t_2218_) == 0)
{
lean_object* v_k_2219_; lean_object* v_l_2220_; lean_object* v_r_2221_; uint8_t v___x_2222_; 
v_k_2219_ = lean_ctor_get(v_t_2218_, 1);
v_l_2220_ = lean_ctor_get(v_t_2218_, 3);
v_r_2221_ = lean_ctor_get(v_t_2218_, 4);
v___x_2222_ = lean_nat_dec_lt(v_k_2217_, v_k_2219_);
if (v___x_2222_ == 0)
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_nat_dec_eq(v_k_2217_, v_k_2219_);
if (v___x_2223_ == 0)
{
v_t_2218_ = v_r_2221_;
goto _start;
}
else
{
return v___x_2223_;
}
}
else
{
v_t_2218_ = v_l_2220_;
goto _start;
}
}
else
{
uint8_t v___x_2226_; 
v___x_2226_ = 0;
return v___x_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg___boxed(lean_object* v_k_2227_, lean_object* v_t_2228_){
_start:
{
uint8_t v_res_2229_; lean_object* v_r_2230_; 
v_res_2229_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(v_k_2227_, v_t_2228_);
lean_dec(v_t_2228_);
lean_dec(v_k_2227_);
v_r_2230_ = lean_box(v_res_2229_);
return v_r_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(lean_object* v_e_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_e_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v_t_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; uint8_t v___x_2480_; 
v___x_2480_ = l_Lean_Expr_hasExprMVar(v_e_2256_);
if (v___x_2480_ == 0)
{
lean_inc_ref(v_e_2256_);
v_t_2297_ = v_e_2256_;
v___y_2298_ = v___y_2257_;
v___y_2299_ = v___y_2258_;
v___y_2300_ = v___y_2259_;
v___y_2301_ = v___y_2260_;
v___y_2302_ = v___y_2261_;
v___y_2303_ = v___y_2262_;
v___y_2304_ = v___y_2263_;
v___y_2305_ = v___y_2264_;
v___y_2306_ = v___y_2265_;
v___y_2307_ = v___y_2266_;
v___y_2308_ = v___y_2267_;
goto v___jp_2296_;
}
else
{
lean_object* v___x_2481_; 
lean_inc_ref(v_e_2256_);
v___x_2481_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2256_, v___y_2265_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v_t_2297_ = v_a_2482_;
v___y_2298_ = v___y_2257_;
v___y_2299_ = v___y_2258_;
v___y_2300_ = v___y_2259_;
v___y_2301_ = v___y_2260_;
v___y_2302_ = v___y_2261_;
v___y_2303_ = v___y_2262_;
v___y_2304_ = v___y_2263_;
v___y_2305_ = v___y_2264_;
v___y_2306_ = v___y_2265_;
v___y_2307_ = v___y_2266_;
v___y_2308_ = v___y_2267_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec_ref(v_e_2256_);
v_a_2483_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2481_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
v___jp_2269_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewVar___redArg(v_e_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2287_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2287_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2279_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2283_);
v___x_2285_ = v___x_2281_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
v_a_2288_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2278_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2278_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
v___jp_2296_:
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = l_Lean_Expr_cleanupAnnotations(v_t_2297_);
lean_dec_ref(v_t_2297_);
v___x_2310_ = l_Lean_Expr_isApp(v___x_2309_);
if (v___x_2310_ == 0)
{
lean_dec_ref(v___x_2309_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2309_);
v___x_2312_ = l_Lean_Expr_isApp(v___x_2311_);
if (v___x_2312_ == 0)
{
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2309_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2311_);
v___x_2314_ = l_Lean_Expr_isApp(v___x_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v___x_2313_);
lean_dec_ref(v___x_2311_);
lean_dec_ref(v___x_2309_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v_arg_2315_; lean_object* v_arg_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v_arg_2315_ = lean_ctor_get(v___x_2309_, 1);
lean_inc_ref(v_arg_2315_);
lean_dec_ref(v___x_2309_);
v_arg_2316_ = lean_ctor_get(v___x_2311_, 1);
lean_inc_ref(v_arg_2316_);
lean_dec_ref(v___x_2311_);
v___x_2317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2313_);
v___x_2318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__2));
v___x_2319_ = l_Lean_Expr_isConstOf(v___x_2317_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__5));
v___x_2321_ = l_Lean_Expr_isConstOf(v___x_2317_, v___x_2320_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; 
v___x_2322_ = l_Lean_Expr_isApp(v___x_2317_);
if (v___x_2322_ == 0)
{
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v___x_2313_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2317_);
lean_dec_ref(v___x_2317_);
v___x_2324_ = l_Lean_Expr_isApp(v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec_ref(v___x_2323_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v___x_2313_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2323_);
lean_dec_ref(v___x_2323_);
v___x_2326_ = l_Lean_Expr_isApp(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v___x_2325_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v___x_2313_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v_arg_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v_arg_2327_ = lean_ctor_get(v___x_2313_, 1);
lean_inc_ref(v_arg_2327_);
lean_dec_ref(v___x_2313_);
v___x_2328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2325_);
lean_dec_ref(v___x_2325_);
v___x_2329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__8));
v___x_2330_ = l_Lean_Expr_isConstOf(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__11));
v___x_2332_ = l_Lean_Expr_isConstOf(v___x_2328_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___closed__14));
v___x_2334_ = l_Lean_Expr_isConstOf(v___x_2328_, v___x_2333_);
lean_dec_ref(v___x_2328_);
if (v___x_2334_ == 0)
{
lean_dec_ref(v_arg_2327_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_2327_, v___y_2306_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; uint8_t v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_unbox(v_a_2336_);
lean_dec(v_a_2336_);
if (v___x_2337_ == 0)
{
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2338_; 
lean_dec_ref(v_e_2256_);
v___x_2338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2316_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2315_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2349_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2349_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2345_, 0, v_a_2339_);
lean_ctor_set(v___x_2345_, 1, v_a_2341_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2347_ = v___x_2343_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
else
{
lean_dec(v_a_2339_);
return v___x_2340_;
}
}
else
{
lean_dec_ref(v_arg_2315_);
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_e_2256_);
v_a_2350_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2335_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2335_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
else
{
lean_object* v___x_2358_; 
lean_dec_ref(v___x_2328_);
v___x_2358_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_2327_, v___y_2306_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; uint8_t v___x_2360_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = lean_unbox(v_a_2359_);
lean_dec(v_a_2359_);
if (v___x_2360_ == 0)
{
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2361_; 
lean_dec_ref(v_e_2256_);
v___x_2361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2316_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2315_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2372_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2372_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2368_, 0, v_a_2362_);
lean_ctor_set(v___x_2368_, 1, v_a_2364_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
else
{
lean_dec(v_a_2362_);
return v___x_2363_;
}
}
else
{
lean_dec_ref(v_arg_2315_);
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_e_2256_);
v_a_2373_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2358_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2358_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_object* v___x_2381_; 
lean_dec_ref(v___x_2328_);
v___x_2381_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_2327_, v___y_2306_);
if (lean_obj_tag(v___x_2381_) == 0)
{
lean_object* v_a_2382_; uint8_t v___x_2383_; 
v_a_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc(v_a_2382_);
lean_dec_ref_known(v___x_2381_, 1);
v___x_2383_ = lean_unbox(v_a_2382_);
lean_dec(v_a_2382_);
if (v___x_2383_ == 0)
{
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2384_; 
lean_inc_ref(v_arg_2316_);
v___x_2384_ = l_Lean_Meta_getIntValue_x3f(v_arg_2316_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref_known(v___x_2384_, 1);
if (lean_obj_tag(v_a_2385_) == 0)
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Meta_getIntValue_x3f(v_arg_2315_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
if (lean_obj_tag(v_a_2387_) == 0)
{
lean_dec_ref(v_arg_2316_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v_e_2256_);
v_val_2388_ = lean_ctor_get(v_a_2387_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v_a_2387_, 1);
v___x_2389_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2316_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2398_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2398_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2394_, 0, v_a_2390_);
lean_ctor_set(v___x_2394_, 1, v_val_2388_);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
else
{
lean_dec(v_val_2388_);
return v___x_2389_;
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_e_2256_);
v_a_2399_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2386_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2386_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_val_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_e_2256_);
v_val_2407_ = lean_ctor_get(v_a_2385_, 0);
lean_inc(v_val_2407_);
lean_dec_ref_known(v_a_2385_, 1);
v___x_2408_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2315_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2417_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2411_ = v___x_2408_;
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2408_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2413_, 0, v_val_2407_);
lean_ctor_set(v___x_2413_, 1, v_a_2409_);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
else
{
lean_dec(v_val_2407_);
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2425_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_e_2256_);
v_a_2418_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2420_ = v___x_2384_;
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2384_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2425_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_e_2256_);
v_a_2426_ = lean_ctor_get(v___x_2381_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2381_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2381_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
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
lean_object* v___x_2434_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v_arg_2316_);
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v___x_2313_);
lean_inc_ref(v_e_2256_);
v___x_2434_ = l_Lean_Meta_getIntValue_x3f(v_e_2256_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2450_; 
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2450_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
if (lean_obj_tag(v_a_2435_) == 1)
{
lean_object* v_val_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_e_2256_);
v_val_2439_ = lean_ctor_get(v_a_2435_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v_a_2435_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2441_ = v_a_2435_;
v_isShared_2442_ = v_isSharedCheck_2449_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_val_2439_);
lean_dec(v_a_2435_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2449_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set_tag(v___x_2441_, 0);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_val_2439_);
v___x_2444_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2446_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2444_);
v___x_2446_ = v___x_2437_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_del_object(v___x_2437_);
lean_dec(v_a_2435_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_e_2256_);
v_a_2451_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2434_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2434_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
}
else
{
lean_object* v___x_2459_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2313_);
v___x_2459_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_2316_, v___y_2306_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v___x_2461_ = lean_unbox(v_a_2460_);
lean_dec(v_a_2460_);
if (v___x_2461_ == 0)
{
lean_dec_ref(v_arg_2315_);
v_e_2270_ = v_e_2256_;
v___y_2271_ = v___y_2298_;
v___y_2272_ = v___y_2303_;
v___y_2273_ = v___y_2304_;
v___y_2274_ = v___y_2305_;
v___y_2275_ = v___y_2306_;
v___y_2276_ = v___y_2307_;
v___y_2277_ = v___y_2308_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2462_; 
lean_dec_ref(v_e_2256_);
v___x_2462_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_arg_2315_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2471_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2471_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2471_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2467_, 0, v_a_2463_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
else
{
return v___x_2462_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_arg_2315_);
lean_dec_ref(v_e_2256_);
v_a_2472_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2459_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2459_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg___boxed(lean_object* v_e_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_e_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec(v___y_2492_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(lean_object* v_k_2505_, lean_object* v_v_2506_, lean_object* v_t_2507_){
_start:
{
if (lean_obj_tag(v_t_2507_) == 0)
{
lean_object* v_size_2508_; lean_object* v_k_2509_; lean_object* v_v_2510_; lean_object* v_l_2511_; lean_object* v_r_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2793_; 
v_size_2508_ = lean_ctor_get(v_t_2507_, 0);
v_k_2509_ = lean_ctor_get(v_t_2507_, 1);
v_v_2510_ = lean_ctor_get(v_t_2507_, 2);
v_l_2511_ = lean_ctor_get(v_t_2507_, 3);
v_r_2512_ = lean_ctor_get(v_t_2507_, 4);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_t_2507_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2514_ = v_t_2507_;
v_isShared_2515_ = v_isSharedCheck_2793_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_r_2512_);
lean_inc(v_l_2511_);
lean_inc(v_v_2510_);
lean_inc(v_k_2509_);
lean_inc(v_size_2508_);
lean_dec(v_t_2507_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2793_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
uint8_t v___x_2516_; 
v___x_2516_ = lean_nat_dec_lt(v_k_2505_, v_k_2509_);
if (v___x_2516_ == 0)
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_eq(v_k_2505_, v_k_2509_);
if (v___x_2517_ == 0)
{
lean_object* v_impl_2518_; lean_object* v___x_2519_; 
lean_dec(v_size_2508_);
v_impl_2518_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(v_k_2505_, v_v_2506_, v_r_2512_);
v___x_2519_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2511_) == 0)
{
lean_object* v_size_2520_; lean_object* v_size_2521_; lean_object* v_k_2522_; lean_object* v_v_2523_; lean_object* v_l_2524_; lean_object* v_r_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; uint8_t v___x_2528_; 
v_size_2520_ = lean_ctor_get(v_l_2511_, 0);
v_size_2521_ = lean_ctor_get(v_impl_2518_, 0);
v_k_2522_ = lean_ctor_get(v_impl_2518_, 1);
v_v_2523_ = lean_ctor_get(v_impl_2518_, 2);
v_l_2524_ = lean_ctor_get(v_impl_2518_, 3);
lean_inc(v_l_2524_);
v_r_2525_ = lean_ctor_get(v_impl_2518_, 4);
v___x_2526_ = lean_unsigned_to_nat(3u);
v___x_2527_ = lean_nat_mul(v___x_2526_, v_size_2520_);
v___x_2528_ = lean_nat_dec_lt(v___x_2527_, v_size_2521_);
lean_dec(v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2532_; 
lean_dec(v_l_2524_);
v___x_2529_ = lean_nat_add(v___x_2519_, v_size_2520_);
v___x_2530_ = lean_nat_add(v___x_2529_, v_size_2521_);
lean_dec(v___x_2529_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_impl_2518_);
lean_ctor_set(v___x_2514_, 0, v___x_2530_);
v___x_2532_ = v___x_2514_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_l_2511_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_impl_2518_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2597_; 
lean_inc(v_r_2525_);
lean_inc(v_v_2523_);
lean_inc(v_k_2522_);
lean_inc(v_size_2521_);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_impl_2518_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; lean_object* v_unused_2602_; 
v_unused_2598_ = lean_ctor_get(v_impl_2518_, 4);
lean_dec(v_unused_2598_);
v_unused_2599_ = lean_ctor_get(v_impl_2518_, 3);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v_impl_2518_, 2);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v_impl_2518_, 1);
lean_dec(v_unused_2601_);
v_unused_2602_ = lean_ctor_get(v_impl_2518_, 0);
lean_dec(v_unused_2602_);
v___x_2535_ = v_impl_2518_;
v_isShared_2536_ = v_isSharedCheck_2597_;
goto v_resetjp_2534_;
}
else
{
lean_dec(v_impl_2518_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2597_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_size_2537_; lean_object* v_k_2538_; lean_object* v_v_2539_; lean_object* v_l_2540_; lean_object* v_r_2541_; lean_object* v_size_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_size_2537_ = lean_ctor_get(v_l_2524_, 0);
v_k_2538_ = lean_ctor_get(v_l_2524_, 1);
v_v_2539_ = lean_ctor_get(v_l_2524_, 2);
v_l_2540_ = lean_ctor_get(v_l_2524_, 3);
v_r_2541_ = lean_ctor_get(v_l_2524_, 4);
v_size_2542_ = lean_ctor_get(v_r_2525_, 0);
v___x_2543_ = lean_unsigned_to_nat(2u);
v___x_2544_ = lean_nat_mul(v___x_2543_, v_size_2542_);
v___x_2545_ = lean_nat_dec_lt(v_size_2537_, v___x_2544_);
lean_dec(v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2573_; 
lean_inc(v_r_2541_);
lean_inc(v_l_2540_);
lean_inc(v_v_2539_);
lean_inc(v_k_2538_);
v_isSharedCheck_2573_ = !lean_is_exclusive(v_l_2524_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; lean_object* v_unused_2575_; lean_object* v_unused_2576_; lean_object* v_unused_2577_; lean_object* v_unused_2578_; 
v_unused_2574_ = lean_ctor_get(v_l_2524_, 4);
lean_dec(v_unused_2574_);
v_unused_2575_ = lean_ctor_get(v_l_2524_, 3);
lean_dec(v_unused_2575_);
v_unused_2576_ = lean_ctor_get(v_l_2524_, 2);
lean_dec(v_unused_2576_);
v_unused_2577_ = lean_ctor_get(v_l_2524_, 1);
lean_dec(v_unused_2577_);
v_unused_2578_ = lean_ctor_get(v_l_2524_, 0);
lean_dec(v_unused_2578_);
v___x_2547_ = v_l_2524_;
v_isShared_2548_ = v_isSharedCheck_2573_;
goto v_resetjp_2546_;
}
else
{
lean_dec(v_l_2524_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2573_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___y_2563_; 
v___x_2549_ = lean_nat_add(v___x_2519_, v_size_2520_);
v___x_2550_ = lean_nat_add(v___x_2549_, v_size_2521_);
lean_dec(v_size_2521_);
if (lean_obj_tag(v_l_2540_) == 0)
{
lean_object* v_size_2571_; 
v_size_2571_ = lean_ctor_get(v_l_2540_, 0);
lean_inc(v_size_2571_);
v___y_2563_ = v_size_2571_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_unsigned_to_nat(0u);
v___y_2563_ = v___x_2572_;
goto v___jp_2562_;
}
v___jp_2551_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2555_ = lean_nat_add(v___y_2552_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec(v___y_2552_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 4, v_r_2525_);
lean_ctor_set(v___x_2547_, 3, v_r_2541_);
lean_ctor_set(v___x_2547_, 2, v_v_2523_);
lean_ctor_set(v___x_2547_, 1, v_k_2522_);
lean_ctor_set(v___x_2547_, 0, v___x_2555_);
v___x_2557_ = v___x_2547_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_k_2522_);
lean_ctor_set(v_reuseFailAlloc_2561_, 2, v_v_2523_);
lean_ctor_set(v_reuseFailAlloc_2561_, 3, v_r_2541_);
lean_ctor_set(v_reuseFailAlloc_2561_, 4, v_r_2525_);
v___x_2557_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 4, v___x_2557_);
lean_ctor_set(v___x_2535_, 3, v___y_2553_);
lean_ctor_set(v___x_2535_, 2, v_v_2539_);
lean_ctor_set(v___x_2535_, 1, v_k_2538_);
lean_ctor_set(v___x_2535_, 0, v___x_2550_);
v___x_2559_ = v___x_2535_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_k_2538_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_v_2539_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v___y_2553_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
v___x_2564_ = lean_nat_add(v___x_2549_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec(v___x_2549_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_l_2540_);
lean_ctor_set(v___x_2514_, 0, v___x_2564_);
v___x_2566_ = v___x_2514_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2564_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2570_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2570_, 3, v_l_2511_);
lean_ctor_set(v_reuseFailAlloc_2570_, 4, v_l_2540_);
v___x_2566_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_nat_add(v___x_2519_, v_size_2542_);
if (lean_obj_tag(v_r_2541_) == 0)
{
lean_object* v_size_2568_; 
v_size_2568_ = lean_ctor_get(v_r_2541_, 0);
lean_inc(v_size_2568_);
v___y_2552_ = v___x_2567_;
v___y_2553_ = v___x_2566_;
v___y_2554_ = v_size_2568_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2569_; 
v___x_2569_ = lean_unsigned_to_nat(0u);
v___y_2552_ = v___x_2567_;
v___y_2553_ = v___x_2566_;
v___y_2554_ = v___x_2569_;
goto v___jp_2551_;
}
}
}
}
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_del_object(v___x_2514_);
v___x_2579_ = lean_nat_add(v___x_2519_, v_size_2520_);
v___x_2580_ = lean_nat_add(v___x_2579_, v_size_2521_);
lean_dec(v_size_2521_);
v___x_2581_ = lean_nat_add(v___x_2579_, v_size_2537_);
lean_dec(v___x_2579_);
lean_inc_ref(v_l_2511_);
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 4, v_l_2524_);
lean_ctor_set(v___x_2535_, 3, v_l_2511_);
lean_ctor_set(v___x_2535_, 2, v_v_2510_);
lean_ctor_set(v___x_2535_, 1, v_k_2509_);
lean_ctor_set(v___x_2535_, 0, v___x_2581_);
v___x_2583_ = v___x_2535_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2581_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2596_, 3, v_l_2511_);
lean_ctor_set(v_reuseFailAlloc_2596_, 4, v_l_2524_);
v___x_2583_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
v_isSharedCheck_2590_ = !lean_is_exclusive(v_l_2511_);
if (v_isSharedCheck_2590_ == 0)
{
lean_object* v_unused_2591_; lean_object* v_unused_2592_; lean_object* v_unused_2593_; lean_object* v_unused_2594_; lean_object* v_unused_2595_; 
v_unused_2591_ = lean_ctor_get(v_l_2511_, 4);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_l_2511_, 3);
lean_dec(v_unused_2592_);
v_unused_2593_ = lean_ctor_get(v_l_2511_, 2);
lean_dec(v_unused_2593_);
v_unused_2594_ = lean_ctor_get(v_l_2511_, 1);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_l_2511_, 0);
lean_dec(v_unused_2595_);
v___x_2585_ = v_l_2511_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_dec(v_l_2511_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 4, v_r_2525_);
lean_ctor_set(v___x_2585_, 3, v___x_2583_);
lean_ctor_set(v___x_2585_, 2, v_v_2523_);
lean_ctor_set(v___x_2585_, 1, v_k_2522_);
lean_ctor_set(v___x_2585_, 0, v___x_2580_);
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_k_2522_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_v_2523_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_r_2525_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2603_; 
v_l_2603_ = lean_ctor_get(v_impl_2518_, 3);
lean_inc(v_l_2603_);
if (lean_obj_tag(v_l_2603_) == 0)
{
lean_object* v_r_2604_; lean_object* v_k_2605_; lean_object* v_v_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2629_; 
v_r_2604_ = lean_ctor_get(v_impl_2518_, 4);
v_k_2605_ = lean_ctor_get(v_impl_2518_, 1);
v_v_2606_ = lean_ctor_get(v_impl_2518_, 2);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_impl_2518_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; lean_object* v_unused_2631_; 
v_unused_2630_ = lean_ctor_get(v_impl_2518_, 3);
lean_dec(v_unused_2630_);
v_unused_2631_ = lean_ctor_get(v_impl_2518_, 0);
lean_dec(v_unused_2631_);
v___x_2608_ = v_impl_2518_;
v_isShared_2609_ = v_isSharedCheck_2629_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_r_2604_);
lean_inc(v_v_2606_);
lean_inc(v_k_2605_);
lean_dec(v_impl_2518_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2629_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_k_2610_; lean_object* v_v_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2625_; 
v_k_2610_ = lean_ctor_get(v_l_2603_, 1);
v_v_2611_ = lean_ctor_get(v_l_2603_, 2);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_l_2603_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; lean_object* v_unused_2628_; 
v_unused_2626_ = lean_ctor_get(v_l_2603_, 4);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_l_2603_, 3);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_l_2603_, 0);
lean_dec(v_unused_2628_);
v___x_2613_ = v_l_2603_;
v_isShared_2614_ = v_isSharedCheck_2625_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_v_2611_);
lean_inc(v_k_2610_);
lean_dec(v_l_2603_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2625_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2615_; lean_object* v___x_2617_; 
v___x_2615_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2604_, 2);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 4, v_r_2604_);
lean_ctor_set(v___x_2613_, 3, v_r_2604_);
lean_ctor_set(v___x_2613_, 2, v_v_2510_);
lean_ctor_set(v___x_2613_, 1, v_k_2509_);
lean_ctor_set(v___x_2613_, 0, v___x_2519_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_r_2604_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v_r_2604_);
v___x_2617_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2619_; 
lean_inc(v_r_2604_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 3, v_r_2604_);
lean_ctor_set(v___x_2608_, 0, v___x_2519_);
v___x_2619_ = v___x_2608_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_k_2605_);
lean_ctor_set(v_reuseFailAlloc_2623_, 2, v_v_2606_);
lean_ctor_set(v_reuseFailAlloc_2623_, 3, v_r_2604_);
lean_ctor_set(v_reuseFailAlloc_2623_, 4, v_r_2604_);
v___x_2619_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v___x_2619_);
lean_ctor_set(v___x_2514_, 3, v___x_2617_);
lean_ctor_set(v___x_2514_, 2, v_v_2611_);
lean_ctor_set(v___x_2514_, 1, v_k_2610_);
lean_ctor_set(v___x_2514_, 0, v___x_2615_);
v___x_2621_ = v___x_2514_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_k_2610_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v_v_2611_);
lean_ctor_set(v_reuseFailAlloc_2622_, 3, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2622_, 4, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
}
else
{
lean_object* v_r_2632_; 
v_r_2632_ = lean_ctor_get(v_impl_2518_, 4);
lean_inc(v_r_2632_);
if (lean_obj_tag(v_r_2632_) == 0)
{
lean_object* v_k_2633_; lean_object* v_v_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2645_; 
v_k_2633_ = lean_ctor_get(v_impl_2518_, 1);
v_v_2634_ = lean_ctor_get(v_impl_2518_, 2);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_impl_2518_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; lean_object* v_unused_2647_; lean_object* v_unused_2648_; 
v_unused_2646_ = lean_ctor_get(v_impl_2518_, 4);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_impl_2518_, 3);
lean_dec(v_unused_2647_);
v_unused_2648_ = lean_ctor_get(v_impl_2518_, 0);
lean_dec(v_unused_2648_);
v___x_2636_ = v_impl_2518_;
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_v_2634_);
lean_inc(v_k_2633_);
lean_dec(v_impl_2518_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2638_ = lean_unsigned_to_nat(3u);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 4, v_l_2603_);
lean_ctor_set(v___x_2636_, 2, v_v_2510_);
lean_ctor_set(v___x_2636_, 1, v_k_2509_);
lean_ctor_set(v___x_2636_, 0, v___x_2519_);
v___x_2640_ = v___x_2636_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_l_2603_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_l_2603_);
v___x_2640_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_r_2632_);
lean_ctor_set(v___x_2514_, 3, v___x_2640_);
lean_ctor_set(v___x_2514_, 2, v_v_2634_);
lean_ctor_set(v___x_2514_, 1, v_k_2633_);
lean_ctor_set(v___x_2514_, 0, v___x_2638_);
v___x_2642_ = v___x_2514_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2633_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2634_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_r_2632_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_unsigned_to_nat(2u);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_impl_2518_);
lean_ctor_set(v___x_2514_, 3, v_r_2632_);
lean_ctor_set(v___x_2514_, 0, v___x_2649_);
v___x_2651_ = v___x_2514_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_r_2632_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_impl_2518_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v___x_2654_; 
lean_dec(v_v_2510_);
lean_dec(v_k_2509_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 2, v_v_2506_);
lean_ctor_set(v___x_2514_, 1, v_k_2505_);
v___x_2654_ = v___x_2514_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_size_2508_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_k_2505_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_v_2506_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_l_2511_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_r_2512_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
else
{
lean_object* v_impl_2656_; lean_object* v___x_2657_; 
lean_dec(v_size_2508_);
v_impl_2656_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(v_k_2505_, v_v_2506_, v_l_2511_);
v___x_2657_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2512_) == 0)
{
lean_object* v_size_2658_; lean_object* v_size_2659_; lean_object* v_k_2660_; lean_object* v_v_2661_; lean_object* v_l_2662_; lean_object* v_r_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v_size_2658_ = lean_ctor_get(v_r_2512_, 0);
v_size_2659_ = lean_ctor_get(v_impl_2656_, 0);
v_k_2660_ = lean_ctor_get(v_impl_2656_, 1);
v_v_2661_ = lean_ctor_get(v_impl_2656_, 2);
v_l_2662_ = lean_ctor_get(v_impl_2656_, 3);
v_r_2663_ = lean_ctor_get(v_impl_2656_, 4);
lean_inc(v_r_2663_);
v___x_2664_ = lean_unsigned_to_nat(3u);
v___x_2665_ = lean_nat_mul(v___x_2664_, v_size_2658_);
v___x_2666_ = lean_nat_dec_lt(v___x_2665_, v_size_2659_);
lean_dec(v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_r_2663_);
v___x_2667_ = lean_nat_add(v___x_2657_, v_size_2659_);
v___x_2668_ = lean_nat_add(v___x_2667_, v_size_2658_);
lean_dec(v___x_2667_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 3, v_impl_2656_);
lean_ctor_set(v___x_2514_, 0, v___x_2668_);
v___x_2670_ = v___x_2514_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2671_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2671_, 3, v_impl_2656_);
lean_ctor_set(v_reuseFailAlloc_2671_, 4, v_r_2512_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
else
{
lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2737_; 
lean_inc(v_l_2662_);
lean_inc(v_v_2661_);
lean_inc(v_k_2660_);
lean_inc(v_size_2659_);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_impl_2656_);
if (v_isSharedCheck_2737_ == 0)
{
lean_object* v_unused_2738_; lean_object* v_unused_2739_; lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2738_ = lean_ctor_get(v_impl_2656_, 4);
lean_dec(v_unused_2738_);
v_unused_2739_ = lean_ctor_get(v_impl_2656_, 3);
lean_dec(v_unused_2739_);
v_unused_2740_ = lean_ctor_get(v_impl_2656_, 2);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_impl_2656_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_impl_2656_, 0);
lean_dec(v_unused_2742_);
v___x_2673_ = v_impl_2656_;
v_isShared_2674_ = v_isSharedCheck_2737_;
goto v_resetjp_2672_;
}
else
{
lean_dec(v_impl_2656_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2737_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_size_2675_; lean_object* v_size_2676_; lean_object* v_k_2677_; lean_object* v_v_2678_; lean_object* v_l_2679_; lean_object* v_r_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v_size_2675_ = lean_ctor_get(v_l_2662_, 0);
v_size_2676_ = lean_ctor_get(v_r_2663_, 0);
v_k_2677_ = lean_ctor_get(v_r_2663_, 1);
v_v_2678_ = lean_ctor_get(v_r_2663_, 2);
v_l_2679_ = lean_ctor_get(v_r_2663_, 3);
v_r_2680_ = lean_ctor_get(v_r_2663_, 4);
v___x_2681_ = lean_unsigned_to_nat(2u);
v___x_2682_ = lean_nat_mul(v___x_2681_, v_size_2675_);
v___x_2683_ = lean_nat_dec_lt(v_size_2676_, v___x_2682_);
lean_dec(v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2712_; 
lean_inc(v_r_2680_);
lean_inc(v_l_2679_);
lean_inc(v_v_2678_);
lean_inc(v_k_2677_);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_r_2663_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; lean_object* v_unused_2716_; lean_object* v_unused_2717_; 
v_unused_2713_ = lean_ctor_get(v_r_2663_, 4);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_r_2663_, 3);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_r_2663_, 2);
lean_dec(v_unused_2715_);
v_unused_2716_ = lean_ctor_get(v_r_2663_, 1);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_r_2663_, 0);
lean_dec(v_unused_2717_);
v___x_2685_ = v_r_2663_;
v_isShared_2686_ = v_isSharedCheck_2712_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_r_2663_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2712_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v___x_2700_; lean_object* v___y_2702_; 
v___x_2687_ = lean_nat_add(v___x_2657_, v_size_2659_);
lean_dec(v_size_2659_);
v___x_2688_ = lean_nat_add(v___x_2687_, v_size_2658_);
lean_dec(v___x_2687_);
v___x_2700_ = lean_nat_add(v___x_2657_, v_size_2675_);
if (lean_obj_tag(v_l_2679_) == 0)
{
lean_object* v_size_2710_; 
v_size_2710_ = lean_ctor_get(v_l_2679_, 0);
lean_inc(v_size_2710_);
v___y_2702_ = v_size_2710_;
goto v___jp_2701_;
}
else
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_unsigned_to_nat(0u);
v___y_2702_ = v___x_2711_;
goto v___jp_2701_;
}
v___jp_2689_:
{
lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2693_ = lean_nat_add(v___y_2690_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec(v___y_2690_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v_r_2512_);
lean_ctor_set(v___x_2685_, 3, v_r_2680_);
lean_ctor_set(v___x_2685_, 2, v_v_2510_);
lean_ctor_set(v___x_2685_, 1, v_k_2509_);
lean_ctor_set(v___x_2685_, 0, v___x_2693_);
v___x_2695_ = v___x_2685_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2693_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_r_2680_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v_r_2512_);
v___x_2695_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2697_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 4, v___x_2695_);
lean_ctor_set(v___x_2673_, 3, v___y_2691_);
lean_ctor_set(v___x_2673_, 2, v_v_2678_);
lean_ctor_set(v___x_2673_, 1, v_k_2677_);
lean_ctor_set(v___x_2673_, 0, v___x_2688_);
v___x_2697_ = v___x_2673_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_k_2677_);
lean_ctor_set(v_reuseFailAlloc_2698_, 2, v_v_2678_);
lean_ctor_set(v_reuseFailAlloc_2698_, 3, v___y_2691_);
lean_ctor_set(v_reuseFailAlloc_2698_, 4, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
v___jp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = lean_nat_add(v___x_2700_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec(v___x_2700_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_l_2679_);
lean_ctor_set(v___x_2514_, 3, v_l_2662_);
lean_ctor_set(v___x_2514_, 2, v_v_2661_);
lean_ctor_set(v___x_2514_, 1, v_k_2660_);
lean_ctor_set(v___x_2514_, 0, v___x_2703_);
v___x_2705_ = v___x_2514_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_k_2660_);
lean_ctor_set(v_reuseFailAlloc_2709_, 2, v_v_2661_);
lean_ctor_set(v_reuseFailAlloc_2709_, 3, v_l_2662_);
lean_ctor_set(v_reuseFailAlloc_2709_, 4, v_l_2679_);
v___x_2705_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_nat_add(v___x_2657_, v_size_2658_);
if (lean_obj_tag(v_r_2680_) == 0)
{
lean_object* v_size_2707_; 
v_size_2707_ = lean_ctor_get(v_r_2680_, 0);
lean_inc(v_size_2707_);
v___y_2690_ = v___x_2706_;
v___y_2691_ = v___x_2705_;
v___y_2692_ = v_size_2707_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_unsigned_to_nat(0u);
v___y_2690_ = v___x_2706_;
v___y_2691_ = v___x_2705_;
v___y_2692_ = v___x_2708_;
goto v___jp_2689_;
}
}
}
}
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
lean_del_object(v___x_2514_);
v___x_2718_ = lean_nat_add(v___x_2657_, v_size_2659_);
lean_dec(v_size_2659_);
v___x_2719_ = lean_nat_add(v___x_2718_, v_size_2658_);
lean_dec(v___x_2718_);
v___x_2720_ = lean_nat_add(v___x_2657_, v_size_2658_);
v___x_2721_ = lean_nat_add(v___x_2720_, v_size_2676_);
lean_dec(v___x_2720_);
lean_inc_ref(v_r_2512_);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 4, v_r_2512_);
lean_ctor_set(v___x_2673_, 3, v_r_2663_);
lean_ctor_set(v___x_2673_, 2, v_v_2510_);
lean_ctor_set(v___x_2673_, 1, v_k_2509_);
lean_ctor_set(v___x_2673_, 0, v___x_2721_);
v___x_2723_ = v___x_2673_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_r_2663_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_r_2512_);
v___x_2723_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
v_isSharedCheck_2730_ = !lean_is_exclusive(v_r_2512_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; lean_object* v_unused_2732_; lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2731_ = lean_ctor_get(v_r_2512_, 4);
lean_dec(v_unused_2731_);
v_unused_2732_ = lean_ctor_get(v_r_2512_, 3);
lean_dec(v_unused_2732_);
v_unused_2733_ = lean_ctor_get(v_r_2512_, 2);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_r_2512_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_r_2512_, 0);
lean_dec(v_unused_2735_);
v___x_2725_ = v_r_2512_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_dec(v_r_2512_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
lean_ctor_set(v___x_2725_, 4, v___x_2723_);
lean_ctor_set(v___x_2725_, 3, v_l_2662_);
lean_ctor_set(v___x_2725_, 2, v_v_2661_);
lean_ctor_set(v___x_2725_, 1, v_k_2660_);
lean_ctor_set(v___x_2725_, 0, v___x_2719_);
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_k_2660_);
lean_ctor_set(v_reuseFailAlloc_2729_, 2, v_v_2661_);
lean_ctor_set(v_reuseFailAlloc_2729_, 3, v_l_2662_);
lean_ctor_set(v_reuseFailAlloc_2729_, 4, v___x_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2743_; 
v_l_2743_ = lean_ctor_get(v_impl_2656_, 3);
if (lean_obj_tag(v_l_2743_) == 0)
{
lean_object* v_r_2744_; lean_object* v_k_2745_; lean_object* v_v_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2757_; 
lean_inc_ref(v_l_2743_);
v_r_2744_ = lean_ctor_get(v_impl_2656_, 4);
v_k_2745_ = lean_ctor_get(v_impl_2656_, 1);
v_v_2746_ = lean_ctor_get(v_impl_2656_, 2);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_impl_2656_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; lean_object* v_unused_2759_; 
v_unused_2758_ = lean_ctor_get(v_impl_2656_, 3);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_impl_2656_, 0);
lean_dec(v_unused_2759_);
v___x_2748_ = v_impl_2656_;
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_r_2744_);
lean_inc(v_v_2746_);
lean_inc(v_k_2745_);
lean_dec(v_impl_2656_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2757_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2744_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 3, v_r_2744_);
lean_ctor_set(v___x_2748_, 2, v_v_2510_);
lean_ctor_set(v___x_2748_, 1, v_k_2509_);
lean_ctor_set(v___x_2748_, 0, v___x_2657_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2756_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2756_, 3, v_r_2744_);
lean_ctor_set(v_reuseFailAlloc_2756_, 4, v_r_2744_);
v___x_2752_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v___x_2752_);
lean_ctor_set(v___x_2514_, 3, v_l_2743_);
lean_ctor_set(v___x_2514_, 2, v_v_2746_);
lean_ctor_set(v___x_2514_, 1, v_k_2745_);
lean_ctor_set(v___x_2514_, 0, v___x_2750_);
v___x_2754_ = v___x_2514_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_k_2745_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v_v_2746_);
lean_ctor_set(v_reuseFailAlloc_2755_, 3, v_l_2743_);
lean_ctor_set(v_reuseFailAlloc_2755_, 4, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
else
{
lean_object* v_r_2760_; 
v_r_2760_ = lean_ctor_get(v_impl_2656_, 4);
lean_inc(v_r_2760_);
if (lean_obj_tag(v_r_2760_) == 0)
{
lean_object* v_k_2761_; lean_object* v_v_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2785_; 
lean_inc(v_l_2743_);
v_k_2761_ = lean_ctor_get(v_impl_2656_, 1);
v_v_2762_ = lean_ctor_get(v_impl_2656_, 2);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_impl_2656_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; lean_object* v_unused_2787_; lean_object* v_unused_2788_; 
v_unused_2786_ = lean_ctor_get(v_impl_2656_, 4);
lean_dec(v_unused_2786_);
v_unused_2787_ = lean_ctor_get(v_impl_2656_, 3);
lean_dec(v_unused_2787_);
v_unused_2788_ = lean_ctor_get(v_impl_2656_, 0);
lean_dec(v_unused_2788_);
v___x_2764_ = v_impl_2656_;
v_isShared_2765_ = v_isSharedCheck_2785_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_v_2762_);
lean_inc(v_k_2761_);
lean_dec(v_impl_2656_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2785_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v_k_2766_; lean_object* v_v_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2781_; 
v_k_2766_ = lean_ctor_get(v_r_2760_, 1);
v_v_2767_ = lean_ctor_get(v_r_2760_, 2);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_r_2760_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; lean_object* v_unused_2783_; lean_object* v_unused_2784_; 
v_unused_2782_ = lean_ctor_get(v_r_2760_, 4);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_r_2760_, 3);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_r_2760_, 0);
lean_dec(v_unused_2784_);
v___x_2769_ = v_r_2760_;
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_v_2767_);
lean_inc(v_k_2766_);
lean_dec(v_r_2760_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2781_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(3u);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 4, v_l_2743_);
lean_ctor_set(v___x_2769_, 3, v_l_2743_);
lean_ctor_set(v___x_2769_, 2, v_v_2762_);
lean_ctor_set(v___x_2769_, 1, v_k_2761_);
lean_ctor_set(v___x_2769_, 0, v___x_2657_);
v___x_2773_ = v___x_2769_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_k_2761_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_v_2762_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_l_2743_);
lean_ctor_set(v_reuseFailAlloc_2780_, 4, v_l_2743_);
v___x_2773_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
lean_object* v___x_2775_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 4, v_l_2743_);
lean_ctor_set(v___x_2764_, 2, v_v_2510_);
lean_ctor_set(v___x_2764_, 1, v_k_2509_);
lean_ctor_set(v___x_2764_, 0, v___x_2657_);
v___x_2775_ = v___x_2764_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v_l_2743_);
lean_ctor_set(v_reuseFailAlloc_2779_, 4, v_l_2743_);
v___x_2775_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2777_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v___x_2775_);
lean_ctor_set(v___x_2514_, 3, v___x_2773_);
lean_ctor_set(v___x_2514_, 2, v_v_2767_);
lean_ctor_set(v___x_2514_, 1, v_k_2766_);
lean_ctor_set(v___x_2514_, 0, v___x_2771_);
v___x_2777_ = v___x_2514_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_k_2766_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v_v_2767_);
lean_ctor_set(v_reuseFailAlloc_2778_, 3, v___x_2773_);
lean_ctor_set(v_reuseFailAlloc_2778_, 4, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2789_ = lean_unsigned_to_nat(2u);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 4, v_r_2760_);
lean_ctor_set(v___x_2514_, 3, v_impl_2656_);
lean_ctor_set(v___x_2514_, 0, v___x_2789_);
v___x_2791_ = v___x_2514_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_k_2509_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_v_2510_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_impl_2656_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v_r_2760_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
lean_ctor_set(v___x_2795_, 1, v_k_2505_);
lean_ctor_set(v___x_2795_, 2, v_v_2506_);
lean_ctor_set(v___x_2795_, 3, v_t_2507_);
lean_ctor_set(v___x_2795_, 4, v_t_2507_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom(lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_getAtom_x3f___redArg(v_e_2796_, v_a_2805_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2940_; 
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2940_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2940_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
if (lean_obj_tag(v_a_2810_) == 1)
{
lean_object* v_val_2814_; lean_object* v_a_2815_; lean_object* v_b_2816_; uint8_t v_isEq_2817_; uint8_t v_isNat_2818_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v_fst_2844_; lean_object* v_snd_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; 
v_val_2814_ = lean_ctor_get(v_a_2810_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v_a_2810_, 1);
v_a_2815_ = lean_ctor_get(v_val_2814_, 0);
lean_inc_ref(v_a_2815_);
v_b_2816_ = lean_ctor_get(v_val_2814_, 1);
lean_inc_ref(v_b_2816_);
v_isEq_2817_ = lean_ctor_get_uint8(v_val_2814_, sizeof(void*)*2);
v_isNat_2818_ = lean_ctor_get_uint8(v_val_2814_, sizeof(void*)*2 + 1);
lean_dec(v_val_2814_);
if (v_isNat_2818_ == 0)
{
v_fst_2844_ = v_a_2815_;
v_snd_2845_ = v_b_2816_;
v___y_2846_ = v_a_2797_;
v___y_2847_ = v_a_2798_;
v___y_2848_ = v_a_2799_;
v___y_2849_ = v_a_2800_;
v___y_2850_ = v_a_2801_;
v___y_2851_ = v_a_2802_;
v___y_2852_ = v_a_2803_;
v___y_2853_ = v_a_2804_;
v___y_2854_ = v_a_2805_;
v___y_2855_ = v_a_2806_;
v___y_2856_ = v_a_2807_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(v_a_2815_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = l_Lean_Meta_Sym_shareCommon(v_a_2897_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = l_Lean_Meta_Grind_Arith_Cutsat_natToIntExpr(v_b_2816_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = l_Lean_Meta_Sym_shareCommon(v_a_2901_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
lean_dec_ref_known(v___x_2902_, 1);
v_fst_2844_ = v_a_2899_;
v_snd_2845_ = v_a_2903_;
v___y_2846_ = v_a_2797_;
v___y_2847_ = v_a_2798_;
v___y_2848_ = v_a_2799_;
v___y_2849_ = v_a_2800_;
v___y_2850_ = v_a_2801_;
v___y_2851_ = v_a_2802_;
v___y_2852_ = v_a_2803_;
v___y_2853_ = v_a_2804_;
v___y_2854_ = v_a_2805_;
v___y_2855_ = v_a_2806_;
v___y_2856_ = v_a_2807_;
goto v___jp_2843_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2899_);
lean_del_object(v___x_2812_);
v_a_2904_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2902_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2899_);
lean_del_object(v___x_2812_);
v_a_2912_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2900_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2900_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v_b_2816_);
lean_del_object(v___x_2812_);
v_a_2920_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2898_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2898_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v_b_2816_);
lean_del_object(v___x_2812_);
v_a_2928_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2896_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2896_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
v___jp_2819_:
{
if (v_isEq_2817_ == 0)
{
lean_object* v___x_2824_; 
lean_dec_ref(v___y_2821_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___y_2822_);
v___x_2824_ = v___x_2812_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___y_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
else
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2842_; 
lean_del_object(v___x_2812_);
v___x_2826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries___closed__1);
v___x_2827_ = l_Int_Internal_Linear_Poly_mul(v___y_2821_, v___x_2826_);
v___x_2828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(v___x_2827_, v___y_2820_);
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2831_ = v___x_2828_;
v_isShared_2832_ = v_isSharedCheck_2842_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2828_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2842_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
uint8_t v___x_2833_; 
v___x_2833_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(v_a_2829_, v___y_2822_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2834_ = lean_box(0);
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(v_a_2829_, v___x_2834_, v___y_2822_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2835_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
else
{
lean_object* v___x_2840_; 
lean_dec(v_a_2829_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___y_2822_);
v___x_2840_ = v___x_2831_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___y_2822_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
}
v___jp_2843_:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_fst_2844_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_snd_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2879_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2879_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2879_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2864_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_a_2858_);
lean_ctor_set(v___x_2864_, 1, v_a_2860_);
v___x_2865_ = l_Int_Internal_Linear_Expr_norm(v___x_2864_);
lean_dec_ref_known(v___x_2864_, 2);
v___x_2866_ = l_Int_Internal_Linear_Poly_getConst(v___x_2865_);
v___x_2867_ = lean_int_neg(v___x_2866_);
lean_dec(v___x_2866_);
v___x_2868_ = l_Int_Internal_Linear_Poly_addConst(v___x_2865_, v___x_2867_);
lean_dec(v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2871_; 
lean_dec_ref_known(v___x_2868_, 1);
lean_del_object(v___x_2812_);
v___x_2869_ = lean_box(1);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2869_);
v___x_2871_ = v___x_2862_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
else
{
lean_object* v___x_2873_; lean_object* v_a_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
lean_del_object(v___x_2862_);
lean_inc_ref(v___x_2868_);
v___x_2873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewDirection___redArg(v___x_2868_, v___y_2846_);
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = lean_box(1);
v___x_2876_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(v_a_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(v_a_2874_, v___x_2877_, v___x_2875_);
v___y_2820_ = v___y_2846_;
v___y_2821_ = v___x_2868_;
v___y_2822_ = v___x_2878_;
goto v___jp_2819_;
}
else
{
lean_dec(v_a_2874_);
v___y_2820_ = v___y_2846_;
v___y_2821_ = v___x_2868_;
v___y_2822_ = v___x_2875_;
goto v___jp_2819_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2858_);
lean_del_object(v___x_2812_);
v_a_2880_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2859_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2859_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v_snd_2845_);
lean_del_object(v___x_2812_);
v_a_2888_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2857_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2857_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
else
{
lean_object* v___x_2936_; lean_object* v___x_2938_; 
lean_dec(v_a_2810_);
v___x_2936_ = lean_box(1);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2936_);
v___x_2938_ = v___x_2812_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
v_a_2941_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2809_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2809_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom___boxed(lean_object* v_e_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom(v_e_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_);
lean_dec(v_a_2960_);
lean_dec_ref(v_a_2959_);
lean_dec(v_a_2958_);
lean_dec_ref(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec_ref(v_a_2955_);
lean_dec(v_a_2954_);
lean_dec_ref(v_a_2953_);
lean_dec(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec(v_a_2950_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0(lean_object* v_e_2963_, lean_object* v_generation_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___redArg(v_e_2963_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0___boxed(lean_object* v_e_2978_, lean_object* v_generation_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__0(v_e_2978_, v_generation_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec(v_generation_2979_);
return v_res_2992_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1(lean_object* v_00_u03b2_2993_, lean_object* v_k_2994_, lean_object* v_t_2995_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___redArg(v_k_2994_, v_t_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1___boxed(lean_object* v_00_u03b2_2997_, lean_object* v_k_2998_, lean_object* v_t_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__1(v_00_u03b2_2997_, v_k_2998_, v_t_2999_);
lean_dec(v_t_2999_);
lean_dec(v_k_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2(lean_object* v_00_u03b2_3002_, lean_object* v_k_3003_, lean_object* v_v_3004_, lean_object* v_t_3005_, lean_object* v_hl_3006_){
_start:
{
lean_object* v___x_3007_; 
v___x_3007_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_previewAtom_spec__2___redArg(v_k_3003_, v_v_3004_, v_t_3005_);
return v___x_3007_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0(lean_object* v_x_3008_, lean_object* v_y_3009_){
_start:
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_nat_dec_lt(v_x_3008_, v_y_3009_);
if (v___x_3010_ == 0)
{
uint8_t v___x_3011_; 
v___x_3011_ = lean_nat_dec_eq(v_x_3008_, v_y_3009_);
if (v___x_3011_ == 0)
{
uint8_t v___x_3012_; 
v___x_3012_ = 2;
return v___x_3012_;
}
else
{
uint8_t v___x_3013_; 
v___x_3013_ = 1;
return v___x_3013_;
}
}
else
{
uint8_t v___x_3014_; 
v___x_3014_ = 0;
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0___boxed(lean_object* v_x_3015_, lean_object* v_y_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__0(v_x_3015_, v_y_3016_);
lean_dec(v_y_3016_);
lean_dec(v_x_3015_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__1(lean_object* v___f_3019_, lean_object* v_x1_3020_, lean_object* v_x2_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DTreeMap_Internal_Impl_union___at___00Std_DTreeMap_union_spec__0___redArg(v___f_3019_, v_x1_3020_, v_x2_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__3(lean_object* v___f_3023_, lean_object* v_x1_3024_, lean_object* v_x2_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Std_DTreeMap_Internal_Impl_inter___at___00Std_DTreeMap_inter_spec__0___redArg(v___f_3023_, v_x1_3024_, v_x2_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2(lean_object* v_supported_3029_, lean_object* v_sub_3030_){
_start:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_apply_1(v_supported_3029_, v_sub_3030_);
v___x_3032_ = lean_unbox(v___x_3031_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2___closed__0));
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_box(0);
return v___x_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0(lean_object* v_x_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = lean_box(0);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0___boxed(lean_object* v_x_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__0(v_x_3037_);
lean_dec_ref(v_x_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_a_3039_, lean_object* v_x_3040_){
_start:
{
if (lean_obj_tag(v_x_3040_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v_key_3042_; lean_object* v_value_3043_; lean_object* v_tail_3044_; uint8_t v___x_3045_; 
v_key_3042_ = lean_ctor_get(v_x_3040_, 0);
v_value_3043_ = lean_ctor_get(v_x_3040_, 1);
v_tail_3044_ = lean_ctor_get(v_x_3040_, 2);
v___x_3045_ = l_Lean_ExprStructEq_beq(v_key_3042_, v_a_3039_);
if (v___x_3045_ == 0)
{
v_x_3040_ = v_tail_3044_;
goto _start;
}
else
{
lean_object* v___x_3047_; 
lean_inc(v_value_3043_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_value_3043_);
return v___x_3047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_3048_, lean_object* v_x_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg(v_a_3048_, v_x_3049_);
lean_dec(v_x_3049_);
lean_dec_ref(v_a_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(lean_object* v_m_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_buckets_3053_; lean_object* v___x_3054_; uint64_t v___x_3055_; uint64_t v___x_3056_; uint64_t v___x_3057_; uint64_t v_fold_3058_; uint64_t v___x_3059_; uint64_t v___x_3060_; uint64_t v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; size_t v___x_3064_; size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_buckets_3053_ = lean_ctor_get(v_m_3051_, 1);
v___x_3054_ = lean_array_get_size(v_buckets_3053_);
v___x_3055_ = l_Lean_ExprStructEq_hash(v_a_3052_);
v___x_3056_ = 32ULL;
v___x_3057_ = lean_uint64_shift_right(v___x_3055_, v___x_3056_);
v_fold_3058_ = lean_uint64_xor(v___x_3055_, v___x_3057_);
v___x_3059_ = 16ULL;
v___x_3060_ = lean_uint64_shift_right(v_fold_3058_, v___x_3059_);
v___x_3061_ = lean_uint64_xor(v_fold_3058_, v___x_3060_);
v___x_3062_ = lean_uint64_to_usize(v___x_3061_);
v___x_3063_ = lean_usize_of_nat(v___x_3054_);
v___x_3064_ = ((size_t)1ULL);
v___x_3065_ = lean_usize_sub(v___x_3063_, v___x_3064_);
v___x_3066_ = lean_usize_land(v___x_3062_, v___x_3065_);
v___x_3067_ = lean_array_uget_borrowed(v_buckets_3053_, v___x_3066_);
v___x_3068_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg(v_a_3052_, v___x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_m_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v_m_3069_, v_a_3070_);
lean_dec_ref(v_a_3070_);
lean_dec_ref(v_m_3069_);
return v_res_3071_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_a_3072_, lean_object* v_x_3073_){
_start:
{
if (lean_obj_tag(v_x_3073_) == 0)
{
uint8_t v___x_3074_; 
v___x_3074_ = 0;
return v___x_3074_;
}
else
{
lean_object* v_key_3075_; lean_object* v_tail_3076_; uint8_t v___x_3077_; 
v_key_3075_ = lean_ctor_get(v_x_3073_, 0);
v_tail_3076_ = lean_ctor_get(v_x_3073_, 2);
v___x_3077_ = l_Lean_ExprStructEq_beq(v_key_3075_, v_a_3072_);
if (v___x_3077_ == 0)
{
v_x_3073_ = v_tail_3076_;
goto _start;
}
else
{
return v___x_3077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_a_3079_, lean_object* v_x_3080_){
_start:
{
uint8_t v_res_3081_; lean_object* v_r_3082_; 
v_res_3081_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3079_, v_x_3080_);
lean_dec(v_x_3080_);
lean_dec_ref(v_a_3079_);
v_r_3082_ = lean_box(v_res_3081_);
return v_r_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
if (lean_obj_tag(v_x_3084_) == 0)
{
return v_x_3083_;
}
else
{
lean_object* v_key_3085_; lean_object* v_value_3086_; lean_object* v_tail_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3110_; 
v_key_3085_ = lean_ctor_get(v_x_3084_, 0);
v_value_3086_ = lean_ctor_get(v_x_3084_, 1);
v_tail_3087_ = lean_ctor_get(v_x_3084_, 2);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_x_3084_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3089_ = v_x_3084_;
v_isShared_3090_ = v_isSharedCheck_3110_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_tail_3087_);
lean_inc(v_value_3086_);
lean_inc(v_key_3085_);
lean_dec(v_x_3084_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3110_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; uint64_t v___x_3092_; uint64_t v___x_3093_; uint64_t v___x_3094_; uint64_t v_fold_3095_; uint64_t v___x_3096_; uint64_t v___x_3097_; uint64_t v___x_3098_; size_t v___x_3099_; size_t v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3106_; 
v___x_3091_ = lean_array_get_size(v_x_3083_);
v___x_3092_ = l_Lean_ExprStructEq_hash(v_key_3085_);
v___x_3093_ = 32ULL;
v___x_3094_ = lean_uint64_shift_right(v___x_3092_, v___x_3093_);
v_fold_3095_ = lean_uint64_xor(v___x_3092_, v___x_3094_);
v___x_3096_ = 16ULL;
v___x_3097_ = lean_uint64_shift_right(v_fold_3095_, v___x_3096_);
v___x_3098_ = lean_uint64_xor(v_fold_3095_, v___x_3097_);
v___x_3099_ = lean_uint64_to_usize(v___x_3098_);
v___x_3100_ = lean_usize_of_nat(v___x_3091_);
v___x_3101_ = ((size_t)1ULL);
v___x_3102_ = lean_usize_sub(v___x_3100_, v___x_3101_);
v___x_3103_ = lean_usize_land(v___x_3099_, v___x_3102_);
v___x_3104_ = lean_array_uget_borrowed(v_x_3083_, v___x_3103_);
lean_inc(v___x_3104_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 2, v___x_3104_);
v___x_3106_ = v___x_3089_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_key_3085_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_value_3086_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_array_uset(v_x_3083_, v___x_3103_, v___x_3106_);
v_x_3083_ = v___x_3107_;
v_x_3084_ = v_tail_3087_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_i_3111_, lean_object* v_source_3112_, lean_object* v_target_3113_){
_start:
{
lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = lean_array_get_size(v_source_3112_);
v___x_3115_ = lean_nat_dec_lt(v_i_3111_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_dec_ref(v_source_3112_);
lean_dec(v_i_3111_);
return v_target_3113_;
}
else
{
lean_object* v_es_3116_; lean_object* v___x_3117_; lean_object* v_source_3118_; lean_object* v_target_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_es_3116_ = lean_array_fget(v_source_3112_, v_i_3111_);
v___x_3117_ = lean_box(0);
v_source_3118_ = lean_array_fset(v_source_3112_, v_i_3111_, v___x_3117_);
v_target_3119_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_target_3113_, v_es_3116_);
v___x_3120_ = lean_unsigned_to_nat(1u);
v___x_3121_ = lean_nat_add(v_i_3111_, v___x_3120_);
lean_dec(v_i_3111_);
v_i_3111_ = v___x_3121_;
v_source_3112_ = v_source_3118_;
v_target_3113_ = v_target_3119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_data_3123_){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v_nbuckets_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3124_ = lean_array_get_size(v_data_3123_);
v___x_3125_ = lean_unsigned_to_nat(2u);
v_nbuckets_3126_ = lean_nat_mul(v___x_3124_, v___x_3125_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_mk_array(v_nbuckets_3126_, v___x_3128_);
v___x_3130_ = lean_array_propagate_mark(v_data_3123_, v___x_3129_);
v___x_3131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v___x_3127_, v_data_3123_, v___x_3130_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_a_3132_, lean_object* v_b_3133_, lean_object* v_x_3134_){
_start:
{
if (lean_obj_tag(v_x_3134_) == 0)
{
lean_dec(v_b_3133_);
lean_dec_ref(v_a_3132_);
return v_x_3134_;
}
else
{
lean_object* v_key_3135_; lean_object* v_value_3136_; lean_object* v_tail_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3149_; 
v_key_3135_ = lean_ctor_get(v_x_3134_, 0);
v_value_3136_ = lean_ctor_get(v_x_3134_, 1);
v_tail_3137_ = lean_ctor_get(v_x_3134_, 2);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_x_3134_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3139_ = v_x_3134_;
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_tail_3137_);
lean_inc(v_value_3136_);
lean_inc(v_key_3135_);
lean_dec(v_x_3134_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3149_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
uint8_t v___x_3141_; 
v___x_3141_ = l_Lean_ExprStructEq_beq(v_key_3135_, v_a_3132_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4___redArg(v_a_3132_, v_b_3133_, v_tail_3137_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 2, v___x_3142_);
v___x_3144_ = v___x_3139_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_key_3135_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_value_3136_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
else
{
lean_object* v___x_3147_; 
lean_dec(v_value_3136_);
lean_dec(v_key_3135_);
if (v_isShared_3140_ == 0)
{
lean_ctor_set(v___x_3139_, 1, v_b_3133_);
lean_ctor_set(v___x_3139_, 0, v_a_3132_);
v___x_3147_ = v___x_3139_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3132_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_b_3133_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_tail_3137_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(lean_object* v_m_3150_, lean_object* v_a_3151_, lean_object* v_b_3152_){
_start:
{
lean_object* v_size_3153_; lean_object* v_buckets_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3197_; 
v_size_3153_ = lean_ctor_get(v_m_3150_, 0);
v_buckets_3154_ = lean_ctor_get(v_m_3150_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_m_3150_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3156_ = v_m_3150_;
v_isShared_3157_ = v_isSharedCheck_3197_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_buckets_3154_);
lean_inc(v_size_3153_);
lean_dec(v_m_3150_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3197_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; uint64_t v___x_3159_; uint64_t v___x_3160_; uint64_t v___x_3161_; uint64_t v_fold_3162_; uint64_t v___x_3163_; uint64_t v___x_3164_; uint64_t v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; size_t v___x_3170_; lean_object* v_bkt_3171_; uint8_t v___x_3172_; 
v___x_3158_ = lean_array_get_size(v_buckets_3154_);
v___x_3159_ = l_Lean_ExprStructEq_hash(v_a_3151_);
v___x_3160_ = 32ULL;
v___x_3161_ = lean_uint64_shift_right(v___x_3159_, v___x_3160_);
v_fold_3162_ = lean_uint64_xor(v___x_3159_, v___x_3161_);
v___x_3163_ = 16ULL;
v___x_3164_ = lean_uint64_shift_right(v_fold_3162_, v___x_3163_);
v___x_3165_ = lean_uint64_xor(v_fold_3162_, v___x_3164_);
v___x_3166_ = lean_uint64_to_usize(v___x_3165_);
v___x_3167_ = lean_usize_of_nat(v___x_3158_);
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_sub(v___x_3167_, v___x_3168_);
v___x_3170_ = lean_usize_land(v___x_3166_, v___x_3169_);
v_bkt_3171_ = lean_array_uget_borrowed(v_buckets_3154_, v___x_3170_);
v___x_3172_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3151_, v_bkt_3171_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v_size_x27_3174_; lean_object* v___x_3175_; lean_object* v_buckets_x27_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; 
v___x_3173_ = lean_unsigned_to_nat(1u);
v_size_x27_3174_ = lean_nat_add(v_size_3153_, v___x_3173_);
lean_dec(v_size_3153_);
lean_inc(v_bkt_3171_);
v___x_3175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3175_, 0, v_a_3151_);
lean_ctor_set(v___x_3175_, 1, v_b_3152_);
lean_ctor_set(v___x_3175_, 2, v_bkt_3171_);
v_buckets_x27_3176_ = lean_array_uset(v_buckets_3154_, v___x_3170_, v___x_3175_);
v___x_3177_ = lean_unsigned_to_nat(4u);
v___x_3178_ = lean_nat_mul(v_size_x27_3174_, v___x_3177_);
v___x_3179_ = lean_unsigned_to_nat(3u);
v___x_3180_ = lean_nat_div(v___x_3178_, v___x_3179_);
lean_dec(v___x_3178_);
v___x_3181_ = lean_array_get_size(v_buckets_x27_3176_);
v___x_3182_ = lean_nat_dec_le(v___x_3180_, v___x_3181_);
lean_dec(v___x_3180_);
if (v___x_3182_ == 0)
{
lean_object* v_val_3183_; lean_object* v___x_3185_; 
v_val_3183_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3___redArg(v_buckets_x27_3176_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v_val_3183_);
lean_ctor_set(v___x_3156_, 0, v_size_x27_3174_);
v___x_3185_ = v___x_3156_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_size_x27_3174_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_val_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
else
{
lean_object* v___x_3188_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v_buckets_x27_3176_);
lean_ctor_set(v___x_3156_, 0, v_size_x27_3174_);
v___x_3188_ = v___x_3156_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_size_x27_3174_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_buckets_x27_3176_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
else
{
lean_object* v___x_3190_; lean_object* v_buckets_x27_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_inc(v_bkt_3171_);
v___x_3190_ = lean_box(0);
v_buckets_x27_3191_ = lean_array_uset(v_buckets_3154_, v___x_3170_, v___x_3190_);
v___x_3192_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4___redArg(v_a_3151_, v_b_3152_, v_bkt_3171_);
v___x_3193_ = lean_array_uset(v_buckets_x27_3191_, v___x_3170_, v___x_3192_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set(v___x_3156_, 1, v___x_3193_);
v___x_3195_ = v___x_3156_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_size_3153_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v___x_3193_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(lean_object* v_atom_3204_, lean_object* v_and_3205_, lean_object* v_or_3206_, lean_object* v_skip_x3f_3207_, lean_object* v_skipConjunct_x3f_3208_, lean_object* v_finishOr_x3f_3209_, lean_object* v_e_3210_, lean_object* v_a_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_a_3225_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_st_ref_get(v_a_3211_);
v___x_3231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v___x_3230_, v_e_3210_);
lean_dec(v___x_3230_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v___x_3232_; 
lean_inc_ref(v_skip_x3f_3207_);
lean_inc_ref(v_e_3210_);
v___x_3232_ = lean_apply_1(v_skip_x3f_3207_, v_e_3210_);
if (lean_obj_tag(v___x_3232_) == 1)
{
lean_object* v_val_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3243_; 
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_dec_ref(v_atom_3204_);
v_val_3233_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3235_ = v___x_3232_;
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_val_3233_);
lean_dec(v___x_3232_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3243_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3237_ = lean_st_ref_take(v_a_3211_);
lean_inc(v_val_3233_);
v___x_3238_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3237_, v_e_3210_, v_val_3233_);
v___x_3239_ = lean_st_ref_put(v_a_3211_, v___x_3238_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 0);
v___x_3241_ = v___x_3235_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_val_3233_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
lean_object* v___x_3244_; uint8_t v___x_3245_; 
lean_dec(v___x_3232_);
v___x_3244_ = l_Lean_Expr_cleanupAnnotations(v_e_3210_);
v___x_3245_ = l_Lean_Expr_isApp(v___x_3244_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; 
lean_dec_ref(v___x_3244_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v_e_3210_);
v___x_3246_ = lean_apply_13(v_atom_3204_, v_e_3210_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v_a_3225_ = v_a_3247_;
goto v___jp_3224_;
}
else
{
lean_dec_ref(v_e_3210_);
return v___x_3246_;
}
}
else
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3244_);
v___x_3249_ = l_Lean_Expr_isApp(v___x_3248_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v_e_3210_);
v___x_3250_ = lean_apply_13(v_atom_3204_, v_e_3210_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
v_a_3225_ = v_a_3251_;
goto v___jp_3224_;
}
else
{
lean_dec_ref(v_e_3210_);
return v___x_3250_;
}
}
else
{
lean_object* v_arg_3252_; lean_object* v_arg_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_arg_3252_ = lean_ctor_get(v___x_3244_, 1);
lean_inc_ref(v_arg_3252_);
lean_dec_ref(v___x_3244_);
v_arg_3253_ = lean_ctor_get(v___x_3248_, 1);
lean_inc_ref(v_arg_3253_);
v___x_3254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3248_);
lean_dec_ref(v___x_3248_);
v___x_3255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1));
v___x_3256_ = l_Lean_Expr_isConstOf(v___x_3254_, v___x_3255_);
if (v___x_3256_ == 0)
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3));
v___x_3258_ = l_Lean_Expr_isConstOf(v___x_3254_, v___x_3257_);
lean_dec_ref(v___x_3254_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
lean_dec_ref(v_arg_3253_);
lean_dec_ref(v_arg_3252_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
lean_inc(v___y_3220_);
lean_inc_ref(v___y_3219_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
lean_inc(v___y_3214_);
lean_inc(v___y_3213_);
lean_inc(v___y_3212_);
lean_inc_ref(v_e_3210_);
v___x_3259_ = lean_apply_13(v_atom_3204_, v_e_3210_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, lean_box(0));
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v_a_3225_ = v_a_3260_;
goto v___jp_3224_;
}
else
{
lean_dec_ref(v_e_3210_);
return v___x_3259_;
}
}
else
{
lean_object* v___x_3261_; 
lean_inc_ref(v_finishOr_x3f_3209_);
lean_inc_ref(v_skip_x3f_3207_);
lean_inc(v_or_3206_);
lean_inc(v_and_3205_);
lean_inc_ref(v_atom_3204_);
lean_inc_ref(v_skipConjunct_x3f_3208_);
v___x_3261_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0(v_skipConjunct_x3f_3208_, v_atom_3204_, v_and_3205_, v_or_3206_, v_skip_x3f_3207_, v_finishOr_x3f_3209_, v_arg_3253_, v_a_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v___x_3263_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v___x_3261_, 1);
lean_inc(v_and_3205_);
v___x_3263_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0(v_skipConjunct_x3f_3208_, v_atom_3204_, v_and_3205_, v_or_3206_, v_skip_x3f_3207_, v_finishOr_x3f_3209_, v_arg_3252_, v_a_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = lean_apply_2(v_and_3205_, v_a_3262_, v_a_3264_);
v_a_3225_ = v___x_3265_;
goto v___jp_3224_;
}
else
{
lean_dec(v_a_3262_);
lean_dec_ref(v_e_3210_);
lean_dec(v_and_3205_);
return v___x_3263_;
}
}
else
{
lean_dec_ref(v_arg_3252_);
lean_dec_ref(v_e_3210_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_dec_ref(v_atom_3204_);
return v___x_3261_;
}
}
}
else
{
lean_object* v___x_3266_; 
lean_dec_ref(v___x_3254_);
lean_inc_ref(v_finishOr_x3f_3209_);
lean_inc_ref(v_skipConjunct_x3f_3208_);
lean_inc_ref(v_skip_x3f_3207_);
lean_inc(v_or_3206_);
lean_inc(v_and_3205_);
lean_inc_ref(v_atom_3204_);
v___x_3266_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3204_, v_and_3205_, v_or_3206_, v_skip_x3f_3207_, v_skipConjunct_x3f_3208_, v_finishOr_x3f_3209_, v_arg_3253_, v_a_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_n(v_a_3267_, 2);
lean_dec_ref_known(v___x_3266_, 1);
lean_inc_ref(v_finishOr_x3f_3209_);
v___x_3268_ = lean_apply_1(v_finishOr_x3f_3209_, v_a_3267_);
if (lean_obj_tag(v___x_3268_) == 1)
{
lean_object* v_val_3269_; 
lean_dec(v_a_3267_);
lean_dec_ref(v_arg_3252_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_dec_ref(v_atom_3204_);
v_val_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_val_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v_a_3225_ = v_val_3269_;
goto v___jp_3224_;
}
else
{
lean_object* v___x_3270_; 
lean_dec(v___x_3268_);
lean_inc(v_or_3206_);
v___x_3270_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3204_, v_and_3205_, v_or_3206_, v_skip_x3f_3207_, v_skipConjunct_x3f_3208_, v_finishOr_x3f_3209_, v_arg_3252_, v_a_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3270_, 1);
v___x_3272_ = lean_apply_2(v_or_3206_, v_a_3267_, v_a_3271_);
v_a_3225_ = v___x_3272_;
goto v___jp_3224_;
}
else
{
lean_dec(v_a_3267_);
lean_dec_ref(v_e_3210_);
lean_dec(v_or_3206_);
return v___x_3270_;
}
}
}
else
{
lean_dec_ref(v_arg_3252_);
lean_dec_ref(v_e_3210_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_dec_ref(v_atom_3204_);
return v___x_3266_;
}
}
}
}
}
}
else
{
lean_object* v_val_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec_ref(v_e_3210_);
lean_dec_ref(v_finishOr_x3f_3209_);
lean_dec_ref(v_skipConjunct_x3f_3208_);
lean_dec_ref(v_skip_x3f_3207_);
lean_dec(v_or_3206_);
lean_dec(v_and_3205_);
lean_dec_ref(v_atom_3204_);
v_val_3273_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3231_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_val_3273_);
lean_dec(v___x_3231_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
lean_ctor_set_tag(v___x_3275_, 0);
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_val_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
v___jp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3226_ = lean_st_ref_take(v_a_3211_);
lean_inc(v_a_3225_);
v___x_3227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3226_, v_e_3210_, v_a_3225_);
v___x_3228_ = lean_st_ref_put(v_a_3211_, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_a_3225_);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0(lean_object* v_skipConjunct_x3f_3281_, lean_object* v_atom_3282_, lean_object* v_and_3283_, lean_object* v_or_3284_, lean_object* v_skip_x3f_3285_, lean_object* v_finishOr_x3f_3286_, lean_object* v_e_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
lean_inc_ref(v_skipConjunct_x3f_3281_);
lean_inc_ref(v_e_3287_);
v___x_3301_ = lean_apply_1(v_skipConjunct_x3f_3281_, v_e_3287_);
if (lean_obj_tag(v___x_3301_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_e_3287_);
lean_dec_ref(v_finishOr_x3f_3286_);
lean_dec_ref(v_skip_x3f_3285_);
lean_dec(v_or_3284_);
lean_dec(v_and_3283_);
lean_dec_ref(v_atom_3282_);
lean_dec_ref(v_skipConjunct_x3f_3281_);
v_val_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_val_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 0);
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_val_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
else
{
lean_object* v___x_3310_; 
lean_dec(v___x_3301_);
v___x_3310_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3282_, v_and_3283_, v_or_3284_, v_skip_x3f_3285_, v_skipConjunct_x3f_3281_, v_finishOr_x3f_3286_, v_e_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_skipConjunct_x3f_3311_ = _args[0];
lean_object* v_atom_3312_ = _args[1];
lean_object* v_and_3313_ = _args[2];
lean_object* v_or_3314_ = _args[3];
lean_object* v_skip_x3f_3315_ = _args[4];
lean_object* v_finishOr_x3f_3316_ = _args[5];
lean_object* v_e_3317_ = _args[6];
lean_object* v___y_3318_ = _args[7];
lean_object* v___y_3319_ = _args[8];
lean_object* v___y_3320_ = _args[9];
lean_object* v___y_3321_ = _args[10];
lean_object* v___y_3322_ = _args[11];
lean_object* v___y_3323_ = _args[12];
lean_object* v___y_3324_ = _args[13];
lean_object* v___y_3325_ = _args[14];
lean_object* v___y_3326_ = _args[15];
lean_object* v___y_3327_ = _args[16];
lean_object* v___y_3328_ = _args[17];
lean_object* v___y_3329_ = _args[18];
lean_object* v___y_3330_ = _args[19];
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___lam__0(v_skipConjunct_x3f_3311_, v_atom_3312_, v_and_3313_, v_or_3314_, v_skip_x3f_3315_, v_finishOr_x3f_3316_, v_e_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3318_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_atom_3332_ = _args[0];
lean_object* v_and_3333_ = _args[1];
lean_object* v_or_3334_ = _args[2];
lean_object* v_skip_x3f_3335_ = _args[3];
lean_object* v_skipConjunct_x3f_3336_ = _args[4];
lean_object* v_finishOr_x3f_3337_ = _args[5];
lean_object* v_e_3338_ = _args[6];
lean_object* v_a_3339_ = _args[7];
lean_object* v___y_3340_ = _args[8];
lean_object* v___y_3341_ = _args[9];
lean_object* v___y_3342_ = _args[10];
lean_object* v___y_3343_ = _args[11];
lean_object* v___y_3344_ = _args[12];
lean_object* v___y_3345_ = _args[13];
lean_object* v___y_3346_ = _args[14];
lean_object* v___y_3347_ = _args[15];
lean_object* v___y_3348_ = _args[16];
lean_object* v___y_3349_ = _args[17];
lean_object* v___y_3350_ = _args[18];
lean_object* v___y_3351_ = _args[19];
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3332_, v_and_3333_, v_or_3334_, v_skip_x3f_3335_, v_skipConjunct_x3f_3336_, v_finishOr_x3f_3337_, v_e_3338_, v_a_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec(v_a_3339_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1(lean_object* v_x_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_box(0);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1___boxed(lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___lam__1(v_x_3355_);
lean_dec(v_x_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg(lean_object* v_atom_3359_, lean_object* v_and_3360_, lean_object* v_or_3361_, lean_object* v_e_3362_, lean_object* v_known_x3f_3363_, lean_object* v_a_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___f_3377_; lean_object* v___f_3378_; lean_object* v___x_3379_; 
v___f_3377_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__0));
v___f_3378_ = ((lean_object*)(l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___closed__1));
v___x_3379_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3359_, v_and_3360_, v_or_3361_, v_known_x3f_3363_, v___f_3377_, v___f_3378_, v_e_3362_, v_a_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_atom_3380_ = _args[0];
lean_object* v_and_3381_ = _args[1];
lean_object* v_or_3382_ = _args[2];
lean_object* v_e_3383_ = _args[3];
lean_object* v_known_x3f_3384_ = _args[4];
lean_object* v_a_3385_ = _args[5];
lean_object* v___y_3386_ = _args[6];
lean_object* v___y_3387_ = _args[7];
lean_object* v___y_3388_ = _args[8];
lean_object* v___y_3389_ = _args[9];
lean_object* v___y_3390_ = _args[10];
lean_object* v___y_3391_ = _args[11];
lean_object* v___y_3392_ = _args[12];
lean_object* v___y_3393_ = _args[13];
lean_object* v___y_3394_ = _args[14];
lean_object* v___y_3395_ = _args[15];
lean_object* v___y_3396_ = _args[16];
lean_object* v___y_3397_ = _args[17];
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg(v_atom_3380_, v_and_3381_, v_or_3382_, v_e_3383_, v_known_x3f_3384_, v_a_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec(v_a_3385_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct(lean_object* v_e_3405_, lean_object* v_supported_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3424_ = l_Lean_Expr_cleanupAnnotations(v_e_3405_);
v___x_3425_ = l_Lean_Expr_isApp(v___x_3424_);
if (v___x_3425_ == 0)
{
lean_dec_ref(v___x_3424_);
lean_dec_ref(v_supported_3406_);
lean_dec_ref(v_e_3405_);
goto v___jp_3420_;
}
else
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3424_);
lean_dec_ref(v___x_3424_);
v___x_3427_ = l_Lean_Expr_isApp(v___x_3426_);
if (v___x_3427_ == 0)
{
lean_dec_ref(v___x_3426_);
lean_dec_ref(v_supported_3406_);
lean_dec_ref(v_e_3405_);
goto v___jp_3420_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v___x_3428_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3426_);
lean_dec_ref(v___x_3426_);
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1));
v___x_3430_ = l_Lean_Expr_isConstOf(v___x_3428_, v___x_3429_);
lean_dec_ref(v___x_3428_);
if (v___x_3430_ == 0)
{
lean_dec_ref(v_supported_3406_);
lean_dec_ref(v_e_3405_);
goto v___jp_3420_;
}
else
{
lean_object* v___f_3431_; lean_object* v___f_3432_; lean_object* v___f_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___f_3431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__1));
v___f_3432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__2));
v___f_3433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___lam__2), 2, 1);
lean_closure_set(v___f_3433_, 0, v_supported_3406_);
v___x_3434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___closed__3));
v___x_3435_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg(v___x_3434_, v___f_3431_, v___f_3432_, v_e_3405_, v___f_3433_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3449_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3438_ = v___x_3435_;
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3435_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3449_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
if (lean_obj_tag(v_a_3436_) == 0)
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
lean_dec_ref_known(v_a_3436_, 5);
v___x_3440_ = lean_box(v___x_3430_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
else
{
uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3444_ = 0;
v___x_3445_ = lean_box(v___x_3444_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3445_);
v___x_3447_ = v___x_3438_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3457_; 
v_a_3450_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3452_ = v___x_3435_;
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3435_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3457_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3455_; 
if (v_isShared_3453_ == 0)
{
v___x_3455_ = v___x_3452_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3450_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
}
v___jp_3420_:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3421_ = 1;
v___x_3422_ = lean_box(v___x_3421_);
v___x_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
return v___x_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct___boxed(lean_object* v_e_3458_, lean_object* v_supported_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct(v_e_3458_, v_supported_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
lean_dec(v_a_3471_);
lean_dec_ref(v_a_3470_);
lean_dec(v_a_3469_);
lean_dec_ref(v_a_3468_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3466_);
lean_dec(v_a_3465_);
lean_dec_ref(v_a_3464_);
lean_dec(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec(v_a_3461_);
lean_dec(v_a_3460_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0(lean_object* v_00_u03c3_3474_, lean_object* v_inst_3475_, lean_object* v_atom_3476_, lean_object* v_and_3477_, lean_object* v_or_3478_, lean_object* v_e_3479_, lean_object* v_known_x3f_3480_, lean_object* v_a_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; 
v___x_3494_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___redArg(v_atom_3476_, v_and_3477_, v_or_3478_, v_e_3479_, v_known_x3f_3480_, v_a_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_3495_ = _args[0];
lean_object* v_inst_3496_ = _args[1];
lean_object* v_atom_3497_ = _args[2];
lean_object* v_and_3498_ = _args[3];
lean_object* v_or_3499_ = _args[4];
lean_object* v_e_3500_ = _args[5];
lean_object* v_known_x3f_3501_ = _args[6];
lean_object* v_a_3502_ = _args[7];
lean_object* v___y_3503_ = _args[8];
lean_object* v___y_3504_ = _args[9];
lean_object* v___y_3505_ = _args[10];
lean_object* v___y_3506_ = _args[11];
lean_object* v___y_3507_ = _args[12];
lean_object* v___y_3508_ = _args[13];
lean_object* v___y_3509_ = _args[14];
lean_object* v___y_3510_ = _args[15];
lean_object* v___y_3511_ = _args[16];
lean_object* v___y_3512_ = _args[17];
lean_object* v___y_3513_ = _args[18];
lean_object* v___y_3514_ = _args[19];
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0(v_00_u03c3_3495_, v_inst_3496_, v_atom_3497_, v_and_3498_, v_or_3499_, v_e_3500_, v_known_x3f_3501_, v_a_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec(v_a_3502_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0(lean_object* v_00_u03c3_3516_, lean_object* v_inst_3517_, lean_object* v_atom_3518_, lean_object* v_and_3519_, lean_object* v_or_3520_, lean_object* v_skip_x3f_3521_, lean_object* v_skipConjunct_x3f_3522_, lean_object* v_finishOr_x3f_3523_, lean_object* v_e_3524_, lean_object* v_a_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg(v_atom_3518_, v_and_3519_, v_or_3520_, v_skip_x3f_3521_, v_skipConjunct_x3f_3522_, v_finishOr_x3f_3523_, v_e_3524_, v_a_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_3539_ = _args[0];
lean_object* v_inst_3540_ = _args[1];
lean_object* v_atom_3541_ = _args[2];
lean_object* v_and_3542_ = _args[3];
lean_object* v_or_3543_ = _args[4];
lean_object* v_skip_x3f_3544_ = _args[5];
lean_object* v_skipConjunct_x3f_3545_ = _args[6];
lean_object* v_finishOr_x3f_3546_ = _args[7];
lean_object* v_e_3547_ = _args[8];
lean_object* v_a_3548_ = _args[9];
lean_object* v___y_3549_ = _args[10];
lean_object* v___y_3550_ = _args[11];
lean_object* v___y_3551_ = _args[12];
lean_object* v___y_3552_ = _args[13];
lean_object* v___y_3553_ = _args[14];
lean_object* v___y_3554_ = _args[15];
lean_object* v___y_3555_ = _args[16];
lean_object* v___y_3556_ = _args[17];
lean_object* v___y_3557_ = _args[18];
lean_object* v___y_3558_ = _args[19];
lean_object* v___y_3559_ = _args[20];
lean_object* v___y_3560_ = _args[21];
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0(v_00_u03c3_3539_, v_inst_3540_, v_atom_3541_, v_and_3542_, v_or_3543_, v_skip_x3f_3544_, v_skipConjunct_x3f_3545_, v_finishOr_x3f_3546_, v_e_3547_, v_a_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec(v_a_3548_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3562_, lean_object* v_m_3563_, lean_object* v_a_3564_, lean_object* v_b_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v_m_3563_, v_a_3564_, v_b_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3567_, lean_object* v_m_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v_m_3568_, v_a_3569_);
return v___x_3570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3571_, lean_object* v_m_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2(v_00_u03b2_3571_, v_m_3572_, v_a_3573_);
lean_dec_ref(v_a_3573_);
lean_dec_ref(v_m_3572_);
return v_res_3574_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_3575_, lean_object* v_a_3576_, lean_object* v_x_3577_){
_start:
{
uint8_t v___x_3578_; 
v___x_3578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3576_, v_x_3577_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_3579_, lean_object* v_a_3580_, lean_object* v_x_3581_){
_start:
{
uint8_t v_res_3582_; lean_object* v_r_3583_; 
v_res_3582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_3579_, v_a_3580_, v_x_3581_);
lean_dec(v_x_3581_);
lean_dec_ref(v_a_3580_);
v_r_3583_ = lean_box(v_res_3582_);
return v_r_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3584_, lean_object* v_data_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3___redArg(v_data_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_3587_, lean_object* v_a_3588_, lean_object* v_b_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__4___redArg(v_a_3588_, v_b_3589_, v_x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_3592_, lean_object* v_a_3593_, lean_object* v_x_3594_){
_start:
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___redArg(v_a_3593_, v_x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_3596_, lean_object* v_a_3597_, lean_object* v_x_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_3596_, v_a_3597_, v_x_3598_);
lean_dec(v_x_3598_);
lean_dec_ref(v_a_3597_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_3600_, lean_object* v_i_3601_, lean_object* v_source_3602_, lean_object* v_target_3603_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4___redArg(v_i_3601_, v_source_3602_, v_target_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_x_3606_, v_x_3607_);
return v___x_3608_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0(uint8_t v_a_3609_, uint8_t v_lia_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v_ordered_3612_; 
v_ordered_3612_ = lean_ctor_get(v_x_3611_, 0);
if (lean_obj_tag(v_ordered_3612_) == 0)
{
return v_a_3609_;
}
else
{
return v_lia_3610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0___boxed(lean_object* v_a_3613_, lean_object* v_lia_3614_, lean_object* v_x_3615_){
_start:
{
uint8_t v_a_81414__boxed_3616_; uint8_t v_lia_boxed_3617_; uint8_t v_res_3618_; lean_object* v_r_3619_; 
v_a_81414__boxed_3616_ = lean_unbox(v_a_3613_);
v_lia_boxed_3617_ = lean_unbox(v_lia_3614_);
v_res_3618_ = l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0(v_a_81414__boxed_3616_, v_lia_boxed_3617_, v_x_3615_);
lean_dec_ref(v_x_3615_);
v_r_3619_ = lean_box(v_res_3618_);
return v_r_3619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1(lean_object* v_a_3620_, lean_object* v_e_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_atomEntries(v_a_3620_, v_e_3621_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1___boxed(lean_object* v_a_3636_, lean_object* v_e_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1(v_a_3636_, v_e_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec(v___y_3638_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2_spec__5(lean_object* v_msg_3652_){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_instInhabitedAdmission;
v___x_3654_ = lean_panic_fn_borrowed(v___x_3653_, v_msg_3652_);
return v___x_3654_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3658_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__2));
v___x_3659_ = lean_unsigned_to_nat(11u);
v___x_3660_ = lean_unsigned_to_nat(163u);
v___x_3661_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__1));
v___x_3662_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__0));
v___x_3663_ = l_mkPanicMessageWithDecl(v___x_3662_, v___x_3661_, v___x_3660_, v___x_3659_, v___x_3658_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2(lean_object* v_a_3664_, lean_object* v_x_3665_){
_start:
{
if (lean_obj_tag(v_x_3665_) == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___closed__3);
v___x_3667_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2_spec__5(v___x_3666_);
return v___x_3667_;
}
else
{
lean_object* v_key_3668_; lean_object* v_value_3669_; lean_object* v_tail_3670_; uint8_t v___x_3671_; 
v_key_3668_ = lean_ctor_get(v_x_3665_, 0);
v_value_3669_ = lean_ctor_get(v_x_3665_, 1);
v_tail_3670_ = lean_ctor_get(v_x_3665_, 2);
v___x_3671_ = l_Lean_ExprStructEq_beq(v_key_3668_, v_a_3664_);
if (v___x_3671_ == 0)
{
v_x_3665_ = v_tail_3670_;
goto _start;
}
else
{
lean_inc(v_value_3669_);
return v_value_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2___boxed(lean_object* v_a_3673_, lean_object* v_x_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2(v_a_3673_, v_x_3674_);
lean_dec(v_x_3674_);
lean_dec_ref(v_a_3673_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1(lean_object* v_m_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_buckets_3678_; lean_object* v___x_3679_; uint64_t v___x_3680_; uint64_t v___x_3681_; uint64_t v___x_3682_; uint64_t v_fold_3683_; uint64_t v___x_3684_; uint64_t v___x_3685_; uint64_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; size_t v___x_3689_; size_t v___x_3690_; size_t v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v_buckets_3678_ = lean_ctor_get(v_m_3676_, 1);
v___x_3679_ = lean_array_get_size(v_buckets_3678_);
v___x_3680_ = l_Lean_ExprStructEq_hash(v_a_3677_);
v___x_3681_ = 32ULL;
v___x_3682_ = lean_uint64_shift_right(v___x_3680_, v___x_3681_);
v_fold_3683_ = lean_uint64_xor(v___x_3680_, v___x_3682_);
v___x_3684_ = 16ULL;
v___x_3685_ = lean_uint64_shift_right(v_fold_3683_, v___x_3684_);
v___x_3686_ = lean_uint64_xor(v_fold_3683_, v___x_3685_);
v___x_3687_ = lean_uint64_to_usize(v___x_3686_);
v___x_3688_ = lean_usize_of_nat(v___x_3679_);
v___x_3689_ = ((size_t)1ULL);
v___x_3690_ = lean_usize_sub(v___x_3688_, v___x_3689_);
v___x_3691_ = lean_usize_land(v___x_3687_, v___x_3690_);
v___x_3692_ = lean_array_uget_borrowed(v_buckets_3678_, v___x_3691_);
v___x_3693_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1_spec__2(v_a_3677_, v___x_3692_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1___boxed(lean_object* v_m_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1(v_m_3694_, v_a_3695_);
lean_dec_ref(v_a_3695_);
lean_dec_ref(v_m_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2(lean_object* v_val_3697_, lean_object* v_empty_3698_, lean_object* v_c_3699_){
_start:
{
lean_object* v___x_3700_; uint8_t v_conjunct_3701_; uint8_t v___x_3702_; uint8_t v___x_3703_; 
v___x_3700_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1(v_val_3697_, v_c_3699_);
v_conjunct_3701_ = lean_ctor_get_uint8(v___x_3700_, 1);
lean_dec_ref(v___x_3700_);
v___x_3702_ = 0;
v___x_3703_ = l_Lean_instBEqLBool_beq(v_conjunct_3701_, v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; 
lean_dec(v_empty_3698_);
v___x_3704_ = lean_box(0);
return v___x_3704_;
}
else
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_empty_3698_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2___boxed(lean_object* v_val_3706_, lean_object* v_empty_3707_, lean_object* v_c_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2(v_val_3706_, v_empty_3707_, v_c_3708_);
lean_dec_ref(v_c_3708_);
lean_dec_ref(v_val_3706_);
return v_res_3709_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0(lean_object* v_val_3710_, lean_object* v_sub_3711_){
_start:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v_val_3710_, v_sub_3711_);
if (lean_obj_tag(v___x_3712_) == 0)
{
uint8_t v___x_3713_; 
v___x_3713_ = 0;
return v___x_3713_;
}
else
{
lean_object* v_val_3714_; uint8_t v_supported_3715_; 
v_val_3714_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_val_3714_);
lean_dec_ref_known(v___x_3712_, 1);
v_supported_3715_ = lean_ctor_get_uint8(v_val_3714_, 0);
lean_dec(v_val_3714_);
return v_supported_3715_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0___boxed(lean_object* v_val_3716_, lean_object* v_sub_3717_){
_start:
{
uint8_t v_res_3718_; lean_object* v_r_3719_; 
v_res_3718_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0(v_val_3716_, v_sub_3717_);
lean_dec_ref(v_sub_3717_);
lean_dec_ref(v_val_3716_);
v_r_3719_ = lean_box(v_res_3718_);
return v_r_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(lean_object* v_canContribute_3720_, lean_object* v_admitConjunct_3721_, lean_object* v_e_3722_, lean_object* v_a_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_supported_3738_; lean_object* v___y_3739_; lean_object* v___x_3746_; lean_object* v_fst_3748_; lean_object* v_snd_3749_; lean_object* v___y_3757_; lean_object* v___x_3760_; 
v___x_3746_ = lean_st_ref_get(v_a_3723_);
v___x_3760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v___x_3746_, v_e_3722_);
lean_dec(v___x_3746_);
if (lean_obj_tag(v___x_3760_) == 1)
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v_e_3722_);
lean_dec_ref(v_admitConjunct_3721_);
lean_dec_ref(v_canContribute_3720_);
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 0);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_val_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
lean_dec(v___x_3760_);
v___x_3769_ = l_Lean_Expr_cleanupAnnotations(v_e_3722_);
v___x_3770_ = l_Lean_Expr_isApp(v___x_3769_);
if (v___x_3770_ == 0)
{
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_admitConjunct_3721_);
v___y_3757_ = v_a_3723_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3771_; uint8_t v___x_3772_; 
v___x_3771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3769_);
v___x_3772_ = l_Lean_Expr_isApp(v___x_3771_);
if (v___x_3772_ == 0)
{
lean_dec_ref(v___x_3771_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v_admitConjunct_3721_);
v___y_3757_ = v_a_3723_;
goto v___jp_3756_;
}
else
{
lean_object* v_arg_3773_; lean_object* v_arg_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v_arg_3773_ = lean_ctor_get(v___x_3769_, 1);
lean_inc_ref(v_arg_3773_);
lean_dec_ref(v___x_3769_);
v_arg_3774_ = lean_ctor_get(v___x_3771_, 1);
lean_inc_ref(v_arg_3774_);
v___x_3775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1));
v___x_3777_ = l_Lean_Expr_isConstOf(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3));
v___x_3779_ = l_Lean_Expr_isConstOf(v___x_3775_, v___x_3778_);
lean_dec_ref(v___x_3775_);
if (v___x_3779_ == 0)
{
lean_dec_ref(v_arg_3774_);
lean_dec_ref(v_arg_3773_);
lean_dec_ref(v_admitConjunct_3721_);
v___y_3757_ = v_a_3723_;
goto v___jp_3756_;
}
else
{
lean_object* v___x_3780_; 
lean_inc_ref(v_admitConjunct_3721_);
lean_inc_ref(v_canContribute_3720_);
v___x_3780_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1(v_canContribute_3720_, v_admitConjunct_3721_, v_arg_3774_, v_a_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___x_3780_, 1);
v___x_3782_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1(v_canContribute_3720_, v_admitConjunct_3721_, v_arg_3773_, v_a_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3782_) == 0)
{
uint8_t v___x_3783_; 
v___x_3783_ = lean_unbox(v_a_3781_);
if (v___x_3783_ == 0)
{
lean_object* v_a_3784_; uint8_t v___x_3785_; 
lean_dec(v_a_3781_);
v_a_3784_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3782_, 1);
v___x_3785_ = lean_unbox(v_a_3784_);
lean_dec(v_a_3784_);
v_supported_3738_ = v___x_3785_;
v___y_3739_ = v_a_3723_;
goto v___jp_3737_;
}
else
{
uint8_t v___x_3786_; 
lean_dec_ref_known(v___x_3782_, 1);
v___x_3786_ = lean_unbox(v_a_3781_);
lean_dec(v_a_3781_);
v_supported_3738_ = v___x_3786_;
v___y_3739_ = v_a_3723_;
goto v___jp_3737_;
}
}
else
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v_a_3781_);
lean_dec_ref(v_e_3722_);
v_a_3787_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3782_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3782_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v_arg_3773_);
lean_dec_ref(v_e_3722_);
lean_dec_ref(v_admitConjunct_3721_);
lean_dec_ref(v_canContribute_3720_);
v_a_3795_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3797_ = v___x_3780_;
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v___x_3780_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3802_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
if (v_isShared_3798_ == 0)
{
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
}
else
{
uint32_t v___x_3803_; uint32_t v___x_3804_; uint8_t v___x_3805_; 
lean_dec_ref(v___x_3775_);
v___x_3803_ = l_Lean_Expr_approxDepth(v_arg_3774_);
v___x_3804_ = l_Lean_Expr_approxDepth(v_arg_3773_);
v___x_3805_ = lean_uint32_dec_le(v___x_3803_, v___x_3804_);
if (v___x_3805_ == 0)
{
v_fst_3748_ = v_arg_3773_;
v_snd_3749_ = v_arg_3774_;
goto v___jp_3747_;
}
else
{
v_fst_3748_ = v_arg_3774_;
v_snd_3749_ = v_arg_3773_;
goto v___jp_3747_;
}
}
}
}
}
v___jp_3737_:
{
uint8_t v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3740_ = 2;
v___x_3741_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3741_, 0, v_supported_3738_);
lean_ctor_set_uint8(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_st_ref_take(v___y_3739_);
lean_inc_ref(v___x_3741_);
v___x_3743_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3742_, v_e_3722_, v___x_3741_);
v___x_3744_ = lean_st_ref_put(v___y_3739_, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3741_);
return v___x_3745_;
}
v___jp_3747_:
{
lean_object* v___x_3750_; 
lean_inc_ref(v_admitConjunct_3721_);
lean_inc_ref(v_canContribute_3720_);
v___x_3750_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(v_canContribute_3720_, v_admitConjunct_3721_, v_fst_3748_, v_a_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; uint8_t v_supported_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v_supported_3752_ = lean_ctor_get_uint8(v_a_3751_, 0);
lean_dec(v_a_3751_);
if (v_supported_3752_ == 0)
{
lean_dec_ref(v_snd_3749_);
lean_dec_ref(v_admitConjunct_3721_);
lean_dec_ref(v_canContribute_3720_);
v_supported_3738_ = v_supported_3752_;
v___y_3739_ = v_a_3723_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3753_; 
v___x_3753_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(v_canContribute_3720_, v_admitConjunct_3721_, v_snd_3749_, v_a_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_object* v_a_3754_; uint8_t v_supported_3755_; 
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref_known(v___x_3753_, 1);
v_supported_3755_ = lean_ctor_get_uint8(v_a_3754_, 0);
lean_dec(v_a_3754_);
v_supported_3738_ = v_supported_3755_;
v___y_3739_ = v_a_3723_;
goto v___jp_3737_;
}
else
{
lean_dec_ref(v_e_3722_);
return v___x_3753_;
}
}
}
else
{
lean_dec_ref(v_snd_3749_);
lean_dec_ref(v_e_3722_);
lean_dec_ref(v_admitConjunct_3721_);
lean_dec_ref(v_canContribute_3720_);
return v___x_3750_;
}
}
v___jp_3756_:
{
lean_object* v___x_3758_; uint8_t v___x_3759_; 
lean_inc_ref(v_e_3722_);
v___x_3758_ = lean_apply_1(v_canContribute_3720_, v_e_3722_);
v___x_3759_ = lean_unbox(v___x_3758_);
v_supported_3738_ = v___x_3759_;
v___y_3739_ = v___y_3757_;
goto v___jp_3737_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1(lean_object* v_canContribute_3806_, lean_object* v_admitConjunct_3807_, lean_object* v_c_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___x_3823_; 
lean_inc_ref(v_c_3808_);
lean_inc_ref(v_admitConjunct_3807_);
v___x_3823_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(v_canContribute_3806_, v_admitConjunct_3807_, v_c_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3866_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3826_ = v___x_3823_;
v_isShared_3827_ = v_isSharedCheck_3866_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3866_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
uint8_t v_supported_3828_; 
v_supported_3828_ = lean_ctor_get_uint8(v_a_3824_, 0);
if (v_supported_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
lean_dec(v_a_3824_);
lean_dec_ref(v_c_3808_);
lean_dec_ref(v_admitConjunct_3807_);
v___x_3829_ = lean_box(v_supported_3828_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3829_);
v___x_3831_ = v___x_3826_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
else
{
uint8_t v_conjunct_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3865_; 
v_conjunct_3833_ = lean_ctor_get_uint8(v_a_3824_, 1);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_a_3824_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3835_ = v_a_3824_;
v_isShared_3836_ = v_isSharedCheck_3865_;
goto v_resetjp_3834_;
}
else
{
lean_dec(v_a_3824_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3865_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
switch(v_conjunct_3833_)
{
case 0:
{
uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3840_; 
lean_del_object(v___x_3835_);
lean_dec_ref(v_c_3808_);
lean_dec_ref(v_admitConjunct_3807_);
v___x_3837_ = 0;
v___x_3838_ = lean_box(v___x_3837_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3838_);
v___x_3840_ = v___x_3826_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3838_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
case 1:
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_del_object(v___x_3835_);
lean_dec_ref(v_c_3808_);
lean_dec_ref(v_admitConjunct_3807_);
v___x_3842_ = lean_box(v_supported_3828_);
if (v_isShared_3827_ == 0)
{
lean_ctor_set(v___x_3826_, 0, v___x_3842_);
v___x_3844_ = v___x_3826_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
default: 
{
lean_object* v___x_3846_; lean_object* v___f_3847_; lean_object* v___x_3848_; 
lean_del_object(v___x_3826_);
v___x_3846_ = lean_st_ref_get(v___y_3809_);
v___f_3847_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3847_, 0, v___x_3846_);
lean_inc(v___y_3821_);
lean_inc_ref(v___y_3820_);
lean_inc(v___y_3819_);
lean_inc_ref(v___y_3818_);
lean_inc(v___y_3817_);
lean_inc_ref(v___y_3816_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
lean_inc(v___y_3812_);
lean_inc(v___y_3811_);
lean_inc(v___y_3810_);
lean_inc_ref(v_c_3808_);
v___x_3848_ = lean_apply_15(v_admitConjunct_3807_, v_c_3808_, v___f_3847_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, lean_box(0));
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3864_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3851_ = v___x_3848_;
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3848_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3864_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3853_; uint8_t v___x_3854_; uint8_t v___x_3855_; lean_object* v___x_3857_; 
v___x_3853_ = lean_st_ref_take(v___y_3809_);
v___x_3854_ = lean_unbox(v_a_3849_);
v___x_3855_ = l_Lean_Bool_toLBool(v___x_3854_);
if (v_isShared_3836_ == 0)
{
v___x_3857_ = v___x_3835_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_3863_, 0, v_supported_3828_);
v___x_3857_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_ctor_set_uint8(v___x_3857_, 1, v___x_3855_);
v___x_3858_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3853_, v_c_3808_, v___x_3857_);
v___x_3859_ = lean_st_ref_put(v___y_3809_, v___x_3858_);
if (v_isShared_3852_ == 0)
{
v___x_3861_ = v___x_3851_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3849_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_del_object(v___x_3835_);
lean_dec_ref(v_c_3808_);
return v___x_3848_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_dec_ref(v_c_3808_);
lean_dec_ref(v_admitConjunct_3807_);
v_a_3867_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3823_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3823_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1___boxed(lean_object** _args){
lean_object* v_canContribute_3875_ = _args[0];
lean_object* v_admitConjunct_3876_ = _args[1];
lean_object* v_c_3877_ = _args[2];
lean_object* v___y_3878_ = _args[3];
lean_object* v___y_3879_ = _args[4];
lean_object* v___y_3880_ = _args[5];
lean_object* v___y_3881_ = _args[6];
lean_object* v___y_3882_ = _args[7];
lean_object* v___y_3883_ = _args[8];
lean_object* v___y_3884_ = _args[9];
lean_object* v___y_3885_ = _args[10];
lean_object* v___y_3886_ = _args[11];
lean_object* v___y_3887_ = _args[12];
lean_object* v___y_3888_ = _args[13];
lean_object* v___y_3889_ = _args[14];
lean_object* v___y_3890_ = _args[15];
lean_object* v___y_3891_ = _args[16];
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___lam__1(v_canContribute_3875_, v_admitConjunct_3876_, v_c_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec(v___y_3878_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0___boxed(lean_object** _args){
lean_object* v_canContribute_3893_ = _args[0];
lean_object* v_admitConjunct_3894_ = _args[1];
lean_object* v_e_3895_ = _args[2];
lean_object* v_a_3896_ = _args[3];
lean_object* v___y_3897_ = _args[4];
lean_object* v___y_3898_ = _args[5];
lean_object* v___y_3899_ = _args[6];
lean_object* v___y_3900_ = _args[7];
lean_object* v___y_3901_ = _args[8];
lean_object* v___y_3902_ = _args[9];
lean_object* v___y_3903_ = _args[10];
lean_object* v___y_3904_ = _args[11];
lean_object* v___y_3905_ = _args[12];
lean_object* v___y_3906_ = _args[13];
lean_object* v___y_3907_ = _args[14];
lean_object* v___y_3908_ = _args[15];
lean_object* v___y_3909_ = _args[16];
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(v_canContribute_3893_, v_admitConjunct_3894_, v_e_3895_, v_a_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec(v_a_3896_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1(lean_object* v_val_3911_, lean_object* v_empty_3912_, lean_object* v_c_3913_){
_start:
{
lean_object* v___x_3914_; uint8_t v_supported_3915_; 
v___x_3914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__1(v_val_3911_, v_c_3913_);
v_supported_3915_ = lean_ctor_get_uint8(v___x_3914_, 0);
lean_dec_ref(v___x_3914_);
if (v_supported_3915_ == 0)
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_empty_3912_);
return v___x_3916_;
}
else
{
lean_object* v___x_3917_; 
lean_dec(v_empty_3912_);
v___x_3917_ = lean_box(0);
return v___x_3917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1___boxed(lean_object* v_val_3918_, lean_object* v_empty_3919_, lean_object* v_c_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1(v_val_3918_, v_empty_3919_, v_c_3920_);
lean_dec_ref(v_c_3920_);
lean_dec_ref(v_val_3918_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(lean_object* v_atom_3922_, lean_object* v_and_3923_, lean_object* v_or_3924_, lean_object* v_skip_x3f_3925_, lean_object* v_skipConjunct_x3f_3926_, lean_object* v_finishOr_x3f_3927_, lean_object* v_e_3928_, lean_object* v_a_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v_a_3944_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = lean_st_ref_get(v_a_3929_);
v___x_3950_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__2___redArg(v___x_3949_, v_e_3928_);
lean_dec(v___x_3949_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v___x_3951_; 
lean_inc_ref(v_skip_x3f_3925_);
lean_inc_ref(v_e_3928_);
v___x_3951_ = lean_apply_1(v_skip_x3f_3925_, v_e_3928_);
if (lean_obj_tag(v___x_3951_) == 1)
{
lean_object* v_val_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3962_; 
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_dec_ref(v_atom_3922_);
v_val_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_val_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3956_ = lean_st_ref_take(v_a_3929_);
lean_inc(v_val_3952_);
v___x_3957_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3956_, v_e_3928_, v_val_3952_);
v___x_3958_ = lean_st_ref_put(v_a_3929_, v___x_3957_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set_tag(v___x_3954_, 0);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_val_3952_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
lean_object* v___x_3963_; uint8_t v___x_3964_; 
lean_dec(v___x_3951_);
v___x_3963_ = l_Lean_Expr_cleanupAnnotations(v_e_3928_);
v___x_3964_ = l_Lean_Expr_isApp(v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; 
lean_dec_ref(v___x_3963_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_inc(v___y_3941_);
lean_inc_ref(v___y_3940_);
lean_inc(v___y_3939_);
lean_inc_ref(v___y_3938_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3936_);
lean_inc(v___y_3935_);
lean_inc_ref(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc_ref(v_e_3928_);
v___x_3965_ = lean_apply_14(v_atom_3922_, v_e_3928_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, lean_box(0));
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v_a_3944_ = v_a_3966_;
goto v___jp_3943_;
}
else
{
lean_dec_ref(v_e_3928_);
return v___x_3965_;
}
}
else
{
lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3963_);
v___x_3968_ = l_Lean_Expr_isApp(v___x_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec_ref(v___x_3967_);
lean_dec_ref(v___x_3963_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_inc(v___y_3941_);
lean_inc_ref(v___y_3940_);
lean_inc(v___y_3939_);
lean_inc_ref(v___y_3938_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3936_);
lean_inc(v___y_3935_);
lean_inc_ref(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc_ref(v_e_3928_);
v___x_3969_ = lean_apply_14(v_atom_3922_, v_e_3928_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, lean_box(0));
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v_a_3944_ = v_a_3970_;
goto v___jp_3943_;
}
else
{
lean_dec_ref(v_e_3928_);
return v___x_3969_;
}
}
else
{
lean_object* v_arg_3971_; lean_object* v_arg_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; 
v_arg_3971_ = lean_ctor_get(v___x_3963_, 1);
lean_inc_ref(v_arg_3971_);
lean_dec_ref(v___x_3963_);
v_arg_3972_ = lean_ctor_get(v___x_3967_, 1);
lean_inc_ref(v_arg_3972_);
v___x_3973_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3967_);
lean_dec_ref(v___x_3967_);
v___x_3974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__1));
v___x_3975_ = l_Lean_Expr_isConstOf(v___x_3973_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; uint8_t v___x_3977_; 
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0___redArg___closed__3));
v___x_3977_ = l_Lean_Expr_isConstOf(v___x_3973_, v___x_3976_);
lean_dec_ref(v___x_3973_);
if (v___x_3977_ == 0)
{
lean_object* v___x_3978_; 
lean_dec_ref(v_arg_3972_);
lean_dec_ref(v_arg_3971_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_inc(v___y_3941_);
lean_inc_ref(v___y_3940_);
lean_inc(v___y_3939_);
lean_inc_ref(v___y_3938_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3936_);
lean_inc(v___y_3935_);
lean_inc_ref(v___y_3934_);
lean_inc(v___y_3933_);
lean_inc(v___y_3932_);
lean_inc(v___y_3931_);
lean_inc(v___y_3930_);
lean_inc_ref(v_e_3928_);
v___x_3978_ = lean_apply_14(v_atom_3922_, v_e_3928_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, lean_box(0));
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
v_a_3944_ = v_a_3979_;
goto v___jp_3943_;
}
else
{
lean_dec_ref(v_e_3928_);
return v___x_3978_;
}
}
else
{
lean_object* v___x_3980_; 
lean_inc_ref(v_finishOr_x3f_3927_);
lean_inc_ref(v_skip_x3f_3925_);
lean_inc(v_or_3924_);
lean_inc(v_and_3923_);
lean_inc_ref(v_atom_3922_);
lean_inc_ref(v_skipConjunct_x3f_3926_);
v___x_3980_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0(v_skipConjunct_x3f_3926_, v_atom_3922_, v_and_3923_, v_or_3924_, v_skip_x3f_3925_, v_finishOr_x3f_3927_, v_arg_3972_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3982_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
lean_inc(v_and_3923_);
v___x_3982_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0(v_skipConjunct_x3f_3926_, v_atom_3922_, v_and_3923_, v_or_3924_, v_skip_x3f_3925_, v_finishOr_x3f_3927_, v_arg_3971_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3984_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v___x_3984_ = lean_apply_2(v_and_3923_, v_a_3981_, v_a_3983_);
v_a_3944_ = v___x_3984_;
goto v___jp_3943_;
}
else
{
lean_dec(v_a_3981_);
lean_dec_ref(v_e_3928_);
lean_dec(v_and_3923_);
return v___x_3982_;
}
}
else
{
lean_dec_ref(v_arg_3971_);
lean_dec_ref(v_e_3928_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_dec_ref(v_atom_3922_);
return v___x_3980_;
}
}
}
else
{
lean_object* v___x_3985_; 
lean_dec_ref(v___x_3973_);
lean_inc_ref(v_finishOr_x3f_3927_);
lean_inc_ref(v_skipConjunct_x3f_3926_);
lean_inc_ref(v_skip_x3f_3925_);
lean_inc(v_or_3924_);
lean_inc(v_and_3923_);
lean_inc_ref(v_atom_3922_);
v___x_3985_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(v_atom_3922_, v_and_3923_, v_or_3924_, v_skip_x3f_3925_, v_skipConjunct_x3f_3926_, v_finishOr_x3f_3927_, v_arg_3972_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v_a_3986_; lean_object* v___x_3987_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc_n(v_a_3986_, 2);
lean_dec_ref_known(v___x_3985_, 1);
lean_inc_ref(v_finishOr_x3f_3927_);
v___x_3987_ = lean_apply_1(v_finishOr_x3f_3927_, v_a_3986_);
if (lean_obj_tag(v___x_3987_) == 1)
{
lean_object* v_val_3988_; 
lean_dec(v_a_3986_);
lean_dec_ref(v_arg_3971_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_dec_ref(v_atom_3922_);
v_val_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_val_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v_a_3944_ = v_val_3988_;
goto v___jp_3943_;
}
else
{
lean_object* v___x_3989_; 
lean_dec(v___x_3987_);
lean_inc(v_or_3924_);
v___x_3989_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(v_atom_3922_, v_and_3923_, v_or_3924_, v_skip_x3f_3925_, v_skipConjunct_x3f_3926_, v_finishOr_x3f_3927_, v_arg_3971_, v_a_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3991_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_a_3990_);
lean_dec_ref_known(v___x_3989_, 1);
v___x_3991_ = lean_apply_2(v_or_3924_, v_a_3986_, v_a_3990_);
v_a_3944_ = v___x_3991_;
goto v___jp_3943_;
}
else
{
lean_dec(v_a_3986_);
lean_dec_ref(v_e_3928_);
lean_dec(v_or_3924_);
return v___x_3989_;
}
}
}
else
{
lean_dec_ref(v_arg_3971_);
lean_dec_ref(v_e_3928_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_dec_ref(v_atom_3922_);
return v___x_3985_;
}
}
}
}
}
}
else
{
lean_object* v_val_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_3999_; 
lean_dec_ref(v_e_3928_);
lean_dec_ref(v_finishOr_x3f_3927_);
lean_dec_ref(v_skipConjunct_x3f_3926_);
lean_dec_ref(v_skip_x3f_3925_);
lean_dec(v_or_3924_);
lean_dec(v_and_3923_);
lean_dec_ref(v_atom_3922_);
v_val_3992_ = lean_ctor_get(v___x_3950_, 0);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3999_ == 0)
{
v___x_3994_ = v___x_3950_;
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_val_3992_);
lean_dec(v___x_3950_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_3999_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 0);
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_val_3992_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
v___jp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3945_ = lean_st_ref_take(v_a_3929_);
lean_inc(v_a_3944_);
v___x_3946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_3945_, v_e_3928_, v_a_3944_);
v___x_3947_ = lean_st_ref_put(v_a_3929_, v___x_3946_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_a_3944_);
return v___x_3948_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0(lean_object* v_skipConjunct_x3f_4000_, lean_object* v_atom_4001_, lean_object* v_and_4002_, lean_object* v_or_4003_, lean_object* v_skip_x3f_4004_, lean_object* v_finishOr_x3f_4005_, lean_object* v_e_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; 
lean_inc_ref(v_skipConjunct_x3f_4000_);
lean_inc_ref(v_e_4006_);
v___x_4021_ = lean_apply_1(v_skipConjunct_x3f_4000_, v_e_4006_);
if (lean_obj_tag(v___x_4021_) == 1)
{
lean_object* v_val_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref(v_e_4006_);
lean_dec_ref(v_finishOr_x3f_4005_);
lean_dec_ref(v_skip_x3f_4004_);
lean_dec(v_or_4003_);
lean_dec(v_and_4002_);
lean_dec_ref(v_atom_4001_);
lean_dec_ref(v_skipConjunct_x3f_4000_);
v_val_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_val_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4029_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
lean_object* v___x_4027_; 
if (v_isShared_4025_ == 0)
{
lean_ctor_set_tag(v___x_4024_, 0);
v___x_4027_ = v___x_4024_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v_val_4022_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
else
{
lean_object* v___x_4030_; 
lean_dec(v___x_4021_);
v___x_4030_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(v_atom_4001_, v_and_4002_, v_or_4003_, v_skip_x3f_4004_, v_skipConjunct_x3f_4000_, v_finishOr_x3f_4005_, v_e_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_skipConjunct_x3f_4031_ = _args[0];
lean_object* v_atom_4032_ = _args[1];
lean_object* v_and_4033_ = _args[2];
lean_object* v_or_4034_ = _args[3];
lean_object* v_skip_x3f_4035_ = _args[4];
lean_object* v_finishOr_x3f_4036_ = _args[5];
lean_object* v_e_4037_ = _args[6];
lean_object* v___y_4038_ = _args[7];
lean_object* v___y_4039_ = _args[8];
lean_object* v___y_4040_ = _args[9];
lean_object* v___y_4041_ = _args[10];
lean_object* v___y_4042_ = _args[11];
lean_object* v___y_4043_ = _args[12];
lean_object* v___y_4044_ = _args[13];
lean_object* v___y_4045_ = _args[14];
lean_object* v___y_4046_ = _args[15];
lean_object* v___y_4047_ = _args[16];
lean_object* v___y_4048_ = _args[17];
lean_object* v___y_4049_ = _args[18];
lean_object* v___y_4050_ = _args[19];
lean_object* v___y_4051_ = _args[20];
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___lam__0(v_skipConjunct_x3f_4031_, v_atom_4032_, v_and_4033_, v_or_4034_, v_skip_x3f_4035_, v_finishOr_x3f_4036_, v_e_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec(v___y_4038_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_atom_4053_ = _args[0];
lean_object* v_and_4054_ = _args[1];
lean_object* v_or_4055_ = _args[2];
lean_object* v_skip_x3f_4056_ = _args[3];
lean_object* v_skipConjunct_x3f_4057_ = _args[4];
lean_object* v_finishOr_x3f_4058_ = _args[5];
lean_object* v_e_4059_ = _args[6];
lean_object* v_a_4060_ = _args[7];
lean_object* v___y_4061_ = _args[8];
lean_object* v___y_4062_ = _args[9];
lean_object* v___y_4063_ = _args[10];
lean_object* v___y_4064_ = _args[11];
lean_object* v___y_4065_ = _args[12];
lean_object* v___y_4066_ = _args[13];
lean_object* v___y_4067_ = _args[14];
lean_object* v___y_4068_ = _args[15];
lean_object* v___y_4069_ = _args[16];
lean_object* v___y_4070_ = _args[17];
lean_object* v___y_4071_ = _args[18];
lean_object* v___y_4072_ = _args[19];
lean_object* v___y_4073_ = _args[20];
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(v_atom_4053_, v_and_4054_, v_or_4055_, v_skip_x3f_4056_, v_skipConjunct_x3f_4057_, v_finishOr_x3f_4058_, v_e_4059_, v_a_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec(v_a_4060_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2(lean_object* v_00_u03c3_4075_, lean_object* v_inst_4076_, lean_object* v_atom_4077_, lean_object* v_and_4078_, lean_object* v_or_4079_, lean_object* v_skip_x3f_4080_, lean_object* v_skipConjunct_x3f_4081_, lean_object* v_finishOr_x3f_4082_, lean_object* v_e_4083_, lean_object* v_a_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___redArg(v_atom_4077_, v_and_4078_, v_or_4079_, v_skip_x3f_4080_, v_skipConjunct_x3f_4081_, v_finishOr_x3f_4082_, v_e_4083_, v_a_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_00_u03c3_4099_ = _args[0];
lean_object* v_inst_4100_ = _args[1];
lean_object* v_atom_4101_ = _args[2];
lean_object* v_and_4102_ = _args[3];
lean_object* v_or_4103_ = _args[4];
lean_object* v_skip_x3f_4104_ = _args[5];
lean_object* v_skipConjunct_x3f_4105_ = _args[6];
lean_object* v_finishOr_x3f_4106_ = _args[7];
lean_object* v_e_4107_ = _args[8];
lean_object* v_a_4108_ = _args[9];
lean_object* v___y_4109_ = _args[10];
lean_object* v___y_4110_ = _args[11];
lean_object* v___y_4111_ = _args[12];
lean_object* v___y_4112_ = _args[13];
lean_object* v___y_4113_ = _args[14];
lean_object* v___y_4114_ = _args[15];
lean_object* v___y_4115_ = _args[16];
lean_object* v___y_4116_ = _args[17];
lean_object* v___y_4117_ = _args[18];
lean_object* v___y_4118_ = _args[19];
lean_object* v___y_4119_ = _args[20];
lean_object* v___y_4120_ = _args[21];
lean_object* v___y_4121_ = _args[22];
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2(v_00_u03c3_4099_, v_inst_4100_, v_atom_4101_, v_and_4102_, v_or_4103_, v_skip_x3f_4104_, v_skipConjunct_x3f_4105_, v_finishOr_x3f_4106_, v_e_4107_, v_a_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec(v_a_4108_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__0(lean_object* v_isEmpty_4123_, lean_object* v_empty_4124_, lean_object* v_x_4125_){
_start:
{
lean_object* v___x_4126_; uint8_t v___x_4127_; 
v___x_4126_ = lean_apply_1(v_isEmpty_4123_, v_x_4125_);
v___x_4127_ = lean_unbox(v___x_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; 
lean_dec(v_empty_4124_);
v___x_4128_ = lean_box(0);
return v___x_4128_;
}
else
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_empty_4124_);
return v___x_4129_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = lean_box(0);
v___x_4131_ = lean_unsigned_to_nat(16u);
v___x_4132_ = lean_mk_array(v___x_4131_, v___x_4130_);
return v___x_4132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__0);
v___x_4134_ = lean_unsigned_to_nat(0u);
v___x_4135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v___x_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg(lean_object* v_x_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1);
v___x_4151_ = lean_st_mk_ref(v___x_4150_);
lean_inc(v___y_4148_);
lean_inc_ref(v___y_4147_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc(v___y_4139_);
lean_inc(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc(v___x_4151_);
v___x_4152_ = lean_apply_14(v_x_4136_, v___x_4151_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, lean_box(0));
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4162_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4162_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4162_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4160_; 
v___x_4157_ = lean_st_ref_get(v___x_4151_);
lean_dec(v___x_4151_);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v_a_4153_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4158_);
v___x_4160_ = v___x_4155_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec(v___x_4151_);
v_a_4163_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4152_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4152_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___boxed(lean_object* v_x_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg(v_x_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
lean_dec(v___y_4181_);
lean_dec_ref(v___y_4180_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec(v___y_4172_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg(lean_object* v_canContribute_4186_, lean_object* v_empty_4187_, lean_object* v_isEmpty_4188_, lean_object* v_atom_4189_, lean_object* v_and_4190_, lean_object* v_or_4191_, lean_object* v_e_4192_, lean_object* v_admitConjunct_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_finishOr_x3f_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_inc(v_empty_4187_);
v_finishOr_x3f_4207_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v_finishOr_x3f_4207_, 0, v_isEmpty_4188_);
lean_closure_set(v_finishOr_x3f_4207_, 1, v_empty_4187_);
v___x_4208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1);
v___x_4209_ = lean_st_mk_ref(v___x_4208_);
lean_inc_ref(v_e_4192_);
v___x_4210_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_inspect___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__0(v_canContribute_4186_, v_admitConjunct_4193_, v_e_4192_, v___x_4209_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4226_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4226_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4226_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4215_; uint8_t v_supported_4216_; 
v___x_4215_ = lean_st_ref_get(v___x_4209_);
lean_dec(v___x_4209_);
v_supported_4216_ = lean_ctor_get_uint8(v_a_4211_, 0);
lean_dec(v_a_4211_);
if (v_supported_4216_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4220_; 
lean_dec(v___x_4215_);
lean_dec_ref(v_finishOr_x3f_4207_);
lean_dec(v_or_4191_);
lean_dec(v_and_4190_);
lean_dec_ref(v_atom_4189_);
lean_inc(v_empty_4187_);
v___x_4217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldCachedM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_admitConjunct_spec__0_spec__0_spec__1___redArg(v___x_4208_, v_e_4192_, v_empty_4187_);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v_empty_4187_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4218_);
v___x_4220_ = v___x_4213_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v___x_4218_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
else
{
lean_object* v_skip_x3f_4222_; lean_object* v_skipConjunct_x3f_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_del_object(v___x_4213_);
lean_inc(v_empty_4187_);
lean_inc(v___x_4215_);
v_skip_x3f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v_skip_x3f_4222_, 0, v___x_4215_);
lean_closure_set(v_skip_x3f_4222_, 1, v_empty_4187_);
v_skipConjunct_x3f_4223_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v_skipConjunct_x3f_4223_, 0, v___x_4215_);
lean_closure_set(v_skipConjunct_x3f_4223_, 1, v_empty_4187_);
v___x_4224_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_visit___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__2___boxed), 23, 9);
lean_closure_set(v___x_4224_, 0, lean_box(0));
lean_closure_set(v___x_4224_, 1, lean_box(0));
lean_closure_set(v___x_4224_, 2, v_atom_4189_);
lean_closure_set(v___x_4224_, 3, v_and_4190_);
lean_closure_set(v___x_4224_, 4, v_or_4191_);
lean_closure_set(v___x_4224_, 5, v_skip_x3f_4222_);
lean_closure_set(v___x_4224_, 6, v_skipConjunct_x3f_4223_);
lean_closure_set(v___x_4224_, 7, v_finishOr_x3f_4207_);
lean_closure_set(v___x_4224_, 8, v_e_4192_);
v___x_4225_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg(v___x_4224_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
return v___x_4225_;
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v___x_4209_);
lean_dec_ref(v_finishOr_x3f_4207_);
lean_dec_ref(v_e_4192_);
lean_dec(v_or_4191_);
lean_dec(v_and_4190_);
lean_dec_ref(v_atom_4189_);
lean_dec(v_empty_4187_);
v_a_4227_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4210_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4210_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_canContribute_4235_ = _args[0];
lean_object* v_empty_4236_ = _args[1];
lean_object* v_isEmpty_4237_ = _args[2];
lean_object* v_atom_4238_ = _args[3];
lean_object* v_and_4239_ = _args[4];
lean_object* v_or_4240_ = _args[5];
lean_object* v_e_4241_ = _args[6];
lean_object* v_admitConjunct_4242_ = _args[7];
lean_object* v___y_4243_ = _args[8];
lean_object* v___y_4244_ = _args[9];
lean_object* v___y_4245_ = _args[10];
lean_object* v___y_4246_ = _args[11];
lean_object* v___y_4247_ = _args[12];
lean_object* v___y_4248_ = _args[13];
lean_object* v___y_4249_ = _args[14];
lean_object* v___y_4250_ = _args[15];
lean_object* v___y_4251_ = _args[16];
lean_object* v___y_4252_ = _args[17];
lean_object* v___y_4253_ = _args[18];
lean_object* v___y_4254_ = _args[19];
lean_object* v___y_4255_ = _args[20];
_start:
{
lean_object* v_res_4256_; 
v_res_4256_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg(v_canContribute_4235_, v_empty_4236_, v_isEmpty_4237_, v_atom_4238_, v_and_4239_, v_or_4240_, v_e_4241_, v_admitConjunct_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec(v___y_4244_);
lean_dec(v___y_4243_);
return v_res_4256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0(lean_object* v_a_4257_, lean_object* v_v_4258_, lean_object* v_sub_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Lean_Meta_Grind_Formula_Summary_find_x3f___redArg(v_a_4257_, v_sub_4259_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v___x_4261_; 
v___x_4261_ = lean_box(0);
return v___x_4261_;
}
else
{
lean_object* v_val_4262_; lean_object* v_lin_4263_; lean_object* v_k_4264_; lean_object* v___x_4265_; 
v_val_4262_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_val_4262_);
lean_dec_ref_known(v___x_4260_, 1);
v_lin_4263_ = lean_ctor_get(v_v_4258_, 0);
v_k_4264_ = lean_ctor_get(v_v_4258_, 1);
v___x_4265_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_Bounds_find_x3f(v_val_4262_, v_lin_4263_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_box(0);
return v___x_4266_;
}
else
{
lean_object* v_val_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4279_; 
v_val_4267_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4269_ = v___x_4265_;
v_isShared_4270_ = v_isSharedCheck_4279_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_val_4267_);
lean_dec(v___x_4265_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4279_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v_snd_4271_; lean_object* v_k_4272_; lean_object* v_atom_4273_; uint8_t v___x_4274_; 
v_snd_4271_ = lean_ctor_get(v_val_4267_, 1);
lean_inc(v_snd_4271_);
lean_dec(v_val_4267_);
v_k_4272_ = lean_ctor_get(v_snd_4271_, 1);
lean_inc(v_k_4272_);
v_atom_4273_ = lean_ctor_get(v_snd_4271_, 2);
lean_inc_ref(v_atom_4273_);
lean_dec(v_snd_4271_);
v___x_4274_ = lean_int_dec_le(v_k_4264_, v_k_4272_);
lean_dec(v_k_4272_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; 
lean_dec_ref(v_atom_4273_);
lean_del_object(v___x_4269_);
v___x_4275_ = lean_box(0);
return v___x_4275_;
}
else
{
lean_object* v___x_4277_; 
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v_atom_4273_);
v___x_4277_ = v___x_4269_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_atom_4273_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0___boxed(lean_object* v_a_4280_, lean_object* v_v_4281_, lean_object* v_sub_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0(v_a_4280_, v_v_4281_, v_sub_4282_);
lean_dec_ref(v_sub_4282_);
lean_dec_ref(v_v_4281_);
lean_dec_ref(v_a_4280_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(lean_object* v_a_4292_, lean_object* v_e_4293_, lean_object* v_init_4294_, lean_object* v_x_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_d_4308_; 
if (lean_obj_tag(v_x_4295_) == 0)
{
lean_object* v_v_4311_; lean_object* v_l_4312_; lean_object* v_r_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; lean_object* v___x_4317_; 
v_v_4311_ = lean_ctor_get(v_x_4295_, 2);
lean_inc_n(v_v_4311_, 2);
v_l_4312_ = lean_ctor_get(v_x_4295_, 3);
lean_inc(v_l_4312_);
v_r_4313_ = lean_ctor_get(v_x_4295_, 4);
lean_inc(v_r_4313_);
lean_dec_ref_known(v_x_4295_, 5);
v___x_4314_ = lean_box(0);
v___x_4315_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__0));
lean_inc_ref_n(v_a_4292_, 2);
v___f_4316_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4316_, 0, v_a_4292_);
lean_closure_set(v___f_4316_, 1, v_v_4311_);
lean_inc_ref(v_e_4293_);
v___x_4317_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(v_a_4292_, v_e_4293_, v_init_4294_, v_l_4312_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
if (lean_obj_tag(v_a_4318_) == 0)
{
lean_object* v_a_4319_; 
lean_dec_ref(v___f_4316_);
lean_dec(v_r_4313_);
lean_dec(v_v_4311_);
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
v_a_4319_ = lean_ctor_get(v_a_4318_, 0);
lean_inc(v_a_4319_);
lean_dec_ref_known(v_a_4318_, 1);
v_d_4308_ = v_a_4319_;
goto v___jp_4307_;
}
else
{
lean_object* v_lin_4320_; lean_object* v_k_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4352_; 
lean_dec_ref_known(v_a_4318_, 1);
v_lin_4320_ = lean_ctor_get(v_v_4311_, 0);
v_k_4321_ = lean_ctor_get(v_v_4311_, 1);
v_isSharedCheck_4352_ = !lean_is_exclusive(v_v_4311_);
if (v_isSharedCheck_4352_ == 0)
{
lean_object* v_unused_4353_; 
v_unused_4353_ = lean_ctor_get(v_v_4311_, 2);
lean_dec(v_unused_4353_);
v___x_4323_ = v_v_4311_;
v_isShared_4324_ = v_isSharedCheck_4352_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_k_4321_);
lean_inc(v_lin_4320_);
lean_dec(v_v_4311_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4352_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4328_; 
v___x_4325_ = l_Int_Internal_Linear_Poly_addConst(v_lin_4320_, v_k_4321_);
lean_dec(v_k_4321_);
lean_inc_ref(v_e_4293_);
v___x_4326_ = lean_alloc_ctor(17, 2, 0);
lean_ctor_set(v___x_4326_, 0, v_e_4293_);
lean_ctor_set(v___x_4326_, 1, v___f_4316_);
if (v_isShared_4324_ == 0)
{
lean_ctor_set(v___x_4323_, 2, v___x_4314_);
lean_ctor_set(v___x_4323_, 1, v___x_4326_);
lean_ctor_set(v___x_4323_, 0, v___x_4325_);
v___x_4328_ = v___x_4323_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4325_);
lean_ctor_set(v_reuseFailAlloc_4351_, 1, v___x_4326_);
lean_ctor_set(v_reuseFailAlloc_4351_, 2, v___x_4314_);
v___x_4328_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
lean_object* v___x_4329_; 
lean_inc(v___y_4305_);
lean_inc_ref(v___y_4304_);
lean_inc(v___y_4303_);
lean_inc_ref(v___y_4302_);
lean_inc(v___y_4301_);
lean_inc_ref(v___y_4300_);
lean_inc(v___y_4299_);
lean_inc_ref(v___y_4298_);
lean_inc(v___y_4297_);
lean_inc(v___y_4296_);
v___x_4329_ = lean_grind_cutsat_assert_le(v___x_4328_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v___x_4330_; 
lean_dec_ref_known(v___x_4329_, 1);
v___x_4330_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v___y_4296_, v___y_4304_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; uint8_t v___x_4332_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = lean_unbox(v_a_4331_);
lean_dec(v_a_4331_);
if (v___x_4332_ == 0)
{
v_init_4294_ = v___x_4315_;
v_x_4295_ = v_r_4313_;
goto _start;
}
else
{
lean_object* v___x_4334_; 
lean_dec(v_r_4313_);
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
v___x_4334_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__2));
v_d_4308_ = v___x_4334_;
goto v___jp_4307_;
}
}
else
{
lean_object* v_a_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4342_; 
lean_dec(v_r_4313_);
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
v_a_4335_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4337_ = v___x_4330_;
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_a_4335_);
lean_dec(v___x_4330_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4342_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4340_; 
if (v_isShared_4338_ == 0)
{
v___x_4340_ = v___x_4337_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
lean_dec(v_r_4313_);
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
v_a_4343_ = lean_ctor_get(v___x_4329_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4329_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4329_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4329_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___f_4316_);
lean_dec(v_r_4313_);
lean_dec(v_v_4311_);
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
return v___x_4317_;
}
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
lean_dec_ref(v_e_4293_);
lean_dec_ref(v_a_4292_);
v___x_4354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_init_4294_);
v___x_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___x_4354_);
return v___x_4355_;
}
v___jp_4307_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v_d_4308_);
v___x_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
return v___x_4310_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___boxed(lean_object* v_a_4356_, lean_object* v_e_4357_, lean_object* v_init_4358_, lean_object* v_x_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(v_a_4356_, v_e_4357_, v_init_4358_, v_x_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec(v___y_4360_);
return v_res_4371_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4376_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(lean_object* v_e_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4381_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4497_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4497_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4497_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
uint8_t v_lia_4395_; 
v_lia_4395_ = lean_ctor_get_uint8(v_a_4391_, sizeof(void*)*18 + 25);
lean_dec(v_a_4391_);
if (v_lia_4395_ == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4398_; 
lean_dec_ref(v_e_4378_);
v___x_4396_ = lean_box(0);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4396_);
v___x_4398_ = v___x_4393_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
else
{
lean_object* v___x_4400_; 
lean_del_object(v___x_4393_);
v___x_4400_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_4379_, v_a_4387_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4488_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4488_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4488_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
uint8_t v___x_4405_; 
v___x_4405_ = lean_unbox(v_a_4401_);
if (v___x_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v___f_4407_; lean_object* v___x_4408_; 
lean_del_object(v___x_4403_);
v___x_4406_ = lean_box(v_lia_4395_);
v___f_4407_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4407_, 0, v_a_4401_);
lean_closure_set(v___f_4407_, 1, v___x_4406_);
v___x_4408_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4378_, v_a_4379_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___f_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___f_4410_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___lam__1___boxed), 15, 1);
lean_closure_set(v___f_4410_, 0, v_a_4409_);
v___x_4411_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__0));
v___x_4412_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default___closed__2);
v___x_4413_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__1));
v___x_4414_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__2));
v___x_4415_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__3));
v___x_4416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg___closed__1);
v___x_4417_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___closed__4);
v___x_4418_ = lean_st_mk_ref(v___x_4417_);
v___x_4419_ = lean_st_mk_ref(v___x_4416_);
lean_inc_ref(v_e_4378_);
v___x_4420_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg(v___x_4411_, v___x_4412_, v___f_4407_, v___f_4410_, v___x_4413_, v___x_4414_, v_e_4378_, v___x_4415_, v___x_4419_, v___x_4418_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = lean_st_ref_get(v___x_4419_);
lean_dec(v___x_4419_);
lean_dec(v___x_4422_);
v___x_4423_ = lean_st_ref_get(v___x_4418_);
lean_dec(v___x_4418_);
lean_dec(v___x_4423_);
v___x_4424_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_4379_, v_a_4387_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4459_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4459_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4459_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
uint8_t v___x_4429_; 
v___x_4429_ = lean_unbox(v_a_4425_);
lean_dec(v_a_4425_);
if (v___x_4429_ == 0)
{
lean_object* v_root_4430_; lean_object* v_ordered_4431_; lean_object* v___x_4432_; lean_object* v_a_4434_; lean_object* v___x_4443_; lean_object* v___x_4444_; 
v_root_4430_ = lean_ctor_get(v_a_4421_, 0);
v_ordered_4431_ = lean_ctor_get(v_root_4430_, 0);
lean_inc(v_ordered_4431_);
v___x_4432_ = lean_box(0);
v___x_4443_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1___closed__0));
v___x_4444_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__1(v_a_4421_, v_e_4378_, v___x_4443_, v_ordered_4431_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v_a_4446_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref_known(v___x_4444_, 1);
v_a_4446_ = lean_ctor_get(v_a_4445_, 0);
lean_inc(v_a_4446_);
lean_dec(v_a_4445_);
v_a_4434_ = v_a_4446_;
goto v___jp_4433_;
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_del_object(v___x_4427_);
v_a_4447_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4444_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4444_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
v___jp_4433_:
{
lean_object* v_fst_4435_; 
v_fst_4435_ = lean_ctor_get(v_a_4434_, 0);
lean_inc(v_fst_4435_);
lean_dec_ref(v_a_4434_);
if (lean_obj_tag(v_fst_4435_) == 0)
{
lean_object* v___x_4437_; 
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4432_);
v___x_4437_ = v___x_4427_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v___x_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
else
{
lean_object* v_val_4439_; lean_object* v___x_4441_; 
v_val_4439_ = lean_ctor_get(v_fst_4435_, 0);
lean_inc(v_val_4439_);
lean_dec_ref_known(v_fst_4435_, 1);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v_val_4439_);
v___x_4441_ = v___x_4427_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_val_4439_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v___x_4455_; lean_object* v___x_4457_; 
lean_dec(v_a_4421_);
lean_dec_ref(v_e_4378_);
v___x_4455_ = lean_box(0);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4455_);
v___x_4457_ = v___x_4427_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v___x_4455_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec(v_a_4421_);
lean_dec_ref(v_e_4378_);
v_a_4460_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4424_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4424_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v___x_4419_);
lean_dec(v___x_4418_);
lean_dec_ref(v_e_4378_);
v_a_4468_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4420_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4420_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___f_4407_);
lean_dec_ref(v_e_4378_);
v_a_4476_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4408_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4408_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v___x_4484_; lean_object* v___x_4486_; 
lean_dec(v_a_4401_);
lean_dec_ref(v_e_4378_);
v___x_4484_ = lean_box(0);
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4484_);
v___x_4486_ = v___x_4403_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v___x_4484_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec_ref(v_e_4378_);
v_a_4489_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4400_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4400_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec_ref(v_e_4378_);
v_a_4498_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4390_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4390_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull___boxed(lean_object* v_e_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_Meta_Grind_Arith_Cutsat_assertOrHull(v_e_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec(v_a_4507_);
return v_res_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3(lean_object* v_00_u03c3_4519_, lean_object* v_x_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___redArg(v_x_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3___boxed(lean_object* v_00_u03c3_4535_, lean_object* v_x_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Meta_Tactic_Grind_Formula_0__Lean_Meta_Grind_Formula_runFold___at___00Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0_spec__3(v_00_u03c3_4535_, v_x_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec(v___y_4537_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(lean_object* v_00_u03c3_4551_, lean_object* v_canContribute_4552_, lean_object* v_empty_4553_, lean_object* v_isEmpty_4554_, lean_object* v_atom_4555_, lean_object* v_and_4556_, lean_object* v_or_4557_, lean_object* v_e_4558_, lean_object* v_admitConjunct_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v___x_4573_; 
v___x_4573_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___redArg(v_canContribute_4552_, v_empty_4553_, v_isEmpty_4554_, v_atom_4555_, v_and_4556_, v_or_4557_, v_e_4558_, v_admitConjunct_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_);
return v___x_4573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03c3_4574_ = _args[0];
lean_object* v_canContribute_4575_ = _args[1];
lean_object* v_empty_4576_ = _args[2];
lean_object* v_isEmpty_4577_ = _args[3];
lean_object* v_atom_4578_ = _args[4];
lean_object* v_and_4579_ = _args[5];
lean_object* v_or_4580_ = _args[6];
lean_object* v_e_4581_ = _args[7];
lean_object* v_admitConjunct_4582_ = _args[8];
lean_object* v___y_4583_ = _args[9];
lean_object* v___y_4584_ = _args[10];
lean_object* v___y_4585_ = _args[11];
lean_object* v___y_4586_ = _args[12];
lean_object* v___y_4587_ = _args[13];
lean_object* v___y_4588_ = _args[14];
lean_object* v___y_4589_ = _args[15];
lean_object* v___y_4590_ = _args[16];
lean_object* v___y_4591_ = _args[17];
lean_object* v___y_4592_ = _args[18];
lean_object* v___y_4593_ = _args[19];
lean_object* v___y_4594_ = _args[20];
lean_object* v___y_4595_ = _args[21];
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_Lean_Meta_Grind_Formula_foldRelevantM___at___00Lean_Meta_Grind_Arith_Cutsat_assertOrHull_spec__0(v_00_u03c3_4574_, v_canContribute_4575_, v_empty_4576_, v_isEmpty_4577_, v_atom_4578_, v_and_4579_, v_or_4580_, v_e_4581_, v_admitConjunct_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec(v___y_4583_);
return v_res_4596_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Formula(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds_default);
l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull_0__Lean_Meta_Grind_Arith_Cutsat_instInhabitedBounds);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Formula(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Formula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_OrHull(builtin);
}
#ifdef __cplusplus
}
#endif
