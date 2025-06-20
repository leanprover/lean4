// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
// Imports: Lean.Meta.Tactic.Grind.ProveEq Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.Proof Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Inv
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
uint8_t l_Int_decidableDvd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_setUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_lm(lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_getMultiplier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0;
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4;
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_propagateEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyAndCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0___boxed(lean_object**);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConstC(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_divConst(lean_object*, lean_object*);
lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___boxed(lean_object**);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_grevlex(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_process_ring_diseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9;
uint64_t l_Lean_Grind_CommRing_hashPoly____x40_Init_Grind_Ring_Poly___hyg_4375_(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addNewDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6;
uint8_t l_Lean_Grind_CommRing_Mon_sharesVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2;
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_simp_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Expr_toPolyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_gcdCoeffs(lean_object*);
static lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1;
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8;
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_setUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___boxed(lean_object**);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_spolM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___Lean_Grind_CommRing_Expr_toPolyM_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4;
LEAN_EXPORT lean_object* lean_process_ring_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findSimp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___boxed(lean_object**);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12;
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_mkDiseqProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
uint8_t l_Lean_Grind_CommRing_beqPoly____x40_Init_Grind_Ring_Poly___hyg_4125_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findSimp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3;
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Poly_divides(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___boxed(lean_object**);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1;
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_Mon_divides(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(x_2, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_nat_dec_eq(x_8, x_13);
lean_dec(x_13);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_6);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_nat_dec_eq(x_8, x_17);
lean_dec(x_17);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(x_1, x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_62; uint8_t x_63; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 14);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_14, 22);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 7);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_17, sizeof(void*)*16);
x_32 = lean_ctor_get(x_17, 8);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 9);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 10);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 11);
lean_inc(x_35);
x_36 = lean_ctor_get(x_17, 12);
lean_inc(x_36);
x_37 = lean_ctor_get(x_17, 13);
lean_inc(x_37);
x_38 = lean_ctor_get(x_17, 15);
lean_inc(x_38);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 lean_ctor_release(x_17, 4);
 lean_ctor_release(x_17, 5);
 lean_ctor_release(x_17, 6);
 lean_ctor_release(x_17, 7);
 lean_ctor_release(x_17, 8);
 lean_ctor_release(x_17, 9);
 lean_ctor_release(x_17, 10);
 lean_ctor_release(x_17, 11);
 lean_ctor_release(x_17, 12);
 lean_ctor_release(x_17, 13);
 lean_ctor_release(x_17, 14);
 lean_ctor_release(x_17, 15);
 x_39 = x_17;
} else {
 lean_dec_ref(x_17);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_18, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_43 = x_18;
} else {
 lean_dec_ref(x_18);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_19, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_19, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_19, 3);
lean_inc(x_47);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 x_48 = x_19;
} else {
 lean_dec_ref(x_19);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Grind_CommRing_Poly_degree(x_1);
x_62 = lean_array_get_size(x_44);
x_63 = lean_nat_dec_lt(x_22, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
x_50 = x_44;
goto block_61;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_array_fget(x_44, x_22);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_64, 22);
x_67 = lean_box(0);
x_68 = lean_array_fset(x_44, x_22, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_66, x_69);
lean_dec(x_66);
lean_ctor_set(x_64, 22, x_70);
x_71 = lean_array_fset(x_68, x_22, x_64);
x_50 = x_71;
goto block_61;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_72 = lean_ctor_get(x_64, 0);
x_73 = lean_ctor_get(x_64, 1);
x_74 = lean_ctor_get(x_64, 2);
x_75 = lean_ctor_get(x_64, 3);
x_76 = lean_ctor_get(x_64, 4);
x_77 = lean_ctor_get(x_64, 5);
x_78 = lean_ctor_get(x_64, 6);
x_79 = lean_ctor_get(x_64, 7);
x_80 = lean_ctor_get(x_64, 8);
x_81 = lean_ctor_get(x_64, 9);
x_82 = lean_ctor_get(x_64, 10);
x_83 = lean_ctor_get(x_64, 11);
x_84 = lean_ctor_get(x_64, 12);
x_85 = lean_ctor_get(x_64, 13);
x_86 = lean_ctor_get(x_64, 14);
x_87 = lean_ctor_get(x_64, 15);
x_88 = lean_ctor_get(x_64, 16);
x_89 = lean_ctor_get(x_64, 17);
x_90 = lean_ctor_get(x_64, 18);
x_91 = lean_ctor_get(x_64, 19);
x_92 = lean_ctor_get(x_64, 20);
x_93 = lean_ctor_get(x_64, 21);
x_94 = lean_ctor_get(x_64, 22);
x_95 = lean_ctor_get(x_64, 23);
x_96 = lean_ctor_get(x_64, 24);
x_97 = lean_ctor_get(x_64, 25);
x_98 = lean_ctor_get(x_64, 26);
x_99 = lean_ctor_get_uint8(x_64, sizeof(void*)*28);
x_100 = lean_ctor_get(x_64, 27);
lean_inc(x_100);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_64);
x_101 = lean_box(0);
x_102 = lean_array_fset(x_44, x_22, x_101);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_94, x_103);
lean_dec(x_94);
x_105 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_105, 0, x_72);
lean_ctor_set(x_105, 1, x_73);
lean_ctor_set(x_105, 2, x_74);
lean_ctor_set(x_105, 3, x_75);
lean_ctor_set(x_105, 4, x_76);
lean_ctor_set(x_105, 5, x_77);
lean_ctor_set(x_105, 6, x_78);
lean_ctor_set(x_105, 7, x_79);
lean_ctor_set(x_105, 8, x_80);
lean_ctor_set(x_105, 9, x_81);
lean_ctor_set(x_105, 10, x_82);
lean_ctor_set(x_105, 11, x_83);
lean_ctor_set(x_105, 12, x_84);
lean_ctor_set(x_105, 13, x_85);
lean_ctor_set(x_105, 14, x_86);
lean_ctor_set(x_105, 15, x_87);
lean_ctor_set(x_105, 16, x_88);
lean_ctor_set(x_105, 17, x_89);
lean_ctor_set(x_105, 18, x_90);
lean_ctor_set(x_105, 19, x_91);
lean_ctor_set(x_105, 20, x_92);
lean_ctor_set(x_105, 21, x_93);
lean_ctor_set(x_105, 22, x_104);
lean_ctor_set(x_105, 23, x_95);
lean_ctor_set(x_105, 24, x_96);
lean_ctor_set(x_105, 25, x_97);
lean_ctor_set(x_105, 26, x_98);
lean_ctor_set(x_105, 27, x_100);
lean_ctor_set_uint8(x_105, sizeof(void*)*28, x_99);
x_106 = lean_array_fset(x_102, x_22, x_105);
x_50 = x_106;
goto block_61;
}
}
block_61:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 4, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_47);
if (lean_is_scalar(x_43)) {
 x_52 = lean_alloc_ctor(0, 4, 0);
} else {
 x_52 = x_43;
}
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_41);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_42);
if (lean_is_scalar(x_39)) {
 x_53 = lean_alloc_ctor(0, 16, 1);
} else {
 x_53 = x_39;
}
lean_ctor_set(x_53, 0, x_23);
lean_ctor_set(x_53, 1, x_24);
lean_ctor_set(x_53, 2, x_25);
lean_ctor_set(x_53, 3, x_26);
lean_ctor_set(x_53, 4, x_27);
lean_ctor_set(x_53, 5, x_28);
lean_ctor_set(x_53, 6, x_29);
lean_ctor_set(x_53, 7, x_30);
lean_ctor_set(x_53, 8, x_32);
lean_ctor_set(x_53, 9, x_33);
lean_ctor_set(x_53, 10, x_34);
lean_ctor_set(x_53, 11, x_35);
lean_ctor_set(x_53, 12, x_36);
lean_ctor_set(x_53, 13, x_37);
lean_ctor_set(x_53, 14, x_52);
lean_ctor_set(x_53, 15, x_38);
lean_ctor_set_uint8(x_53, sizeof(void*)*16, x_31);
x_54 = lean_st_ref_set(x_4, x_53, x_20);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_2);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_21);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_2);
lean_ctor_set(x_59, 2, x_49);
lean_ctor_set(x_59, 3, x_21);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_13);
if (x_107 == 0)
{
return x_13;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_13, 0);
x_109 = lean_ctor_get(x_13, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_13);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to convert to ring expression", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 20);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 21);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_16, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_12);
x_20 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*6 + 11);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1;
x_29 = l_Lean_indentExpr(x_1);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Meta_Grind_reportIssue(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_18);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_19);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_19, 0, x_40);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_19, 0);
lean_inc(x_41);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_12, 0, x_43);
return x_12;
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_1);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_ctor_get(x_44, 20);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 21);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_1);
x_48 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_47, x_1);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_inc(x_1);
x_49 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_46, x_1);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*6 + 11);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1;
x_58 = l_Lean_indentExpr(x_1);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_Grind_reportIssue(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
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
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_66 = lean_ctor_get(x_49, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_67 = x_49;
} else {
 lean_dec_ref(x_49);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_66);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_45);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_46);
lean_dec(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_48);
lean_ctor_set(x_71, 1, x_45);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_12);
if (x_72 == 0)
{
return x_12;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_12, 0);
x_74 = lean_ctor_get(x_12, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_12);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_22; 
lean_dec(x_8);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
if (x_5 == 0)
{
goto block_21;
}
else
{
if (x_6 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_22 = x_27;
goto block_25;
}
else
{
goto block_21;
}
}
block_21:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
x_15 = l_Lean_Grind_CommRing_Poly_divides(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_2;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_13;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
block_25:
{
uint8_t x_23; 
x_23 = l_Int_decidableDvd(x_22, x_4);
lean_dec(x_22);
if (x_23 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_2);
{
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_2;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
goto block_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findSimp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(x_3, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 25);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0;
x_25 = lean_unbox(x_14);
lean_dec(x_14);
x_26 = lean_unbox(x_17);
lean_dec(x_17);
x_27 = l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg(x_2, x_24, x_23, x_1, x_25, x_26, x_22, x_24, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_17);
lean_dec(x_14);
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
lean_dec(x_14);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = lean_unbox(x_6);
lean_dec(x_6);
x_12 = l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_5);
lean_dec(x_5);
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_List_forIn_x27_loop___at___Lean_Grind_CommRing_Mon_findSimp_x3f_spec__0(x_1, x_2, x_3, x_4, x_21, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_findSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Grind_CommRing_Mon_findSimp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
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
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findSimp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = l_Lean_Grind_CommRing_Mon_findSimp_x3f(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_16;
x_11 = x_19;
goto _start;
}
else
{
lean_dec(x_18);
return x_17;
}
}
else
{
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_findSimp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Grind_CommRing_Poly_findSimp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ring", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_21; 
x_21 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___Lean_Grind_CommRing_Expr_toPolyM_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_126; 
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
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
x_25 = x_126;
goto block_125;
block_125:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = l_Lean_Grind_CommRing_Poly_simp_x3f(x_25, x_26, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_2);
if (lean_is_scalar(x_24)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_24;
}
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(x_4, x_23);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_34 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
x_35 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_34, x_10, x_32);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_30);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_29, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_29, 3);
lean_inc(x_42);
lean_dec(x_29);
x_13 = x_39;
x_14 = x_40;
x_15 = x_41;
x_16 = x_42;
x_17 = x_38;
goto block_20;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 1);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_29, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_29, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_29, 3);
lean_inc(x_51);
lean_dec(x_29);
lean_inc(x_48);
x_52 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_56 = l_Lean_MessageData_ofExpr(x_53);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_56);
lean_ctor_set(x_35, 0, x_55);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_55);
lean_ctor_set(x_30, 0, x_35);
x_57 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_34, x_30, x_8, x_9, x_10, x_11, x_54);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_13 = x_48;
x_14 = x_49;
x_15 = x_50;
x_16 = x_51;
x_17 = x_58;
goto block_20;
}
else
{
uint8_t x_59; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_free_object(x_35);
lean_free_object(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_35);
lean_free_object(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_46);
if (x_63 == 0)
{
return x_46;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_46);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_dec(x_35);
x_68 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_29, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_29, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_29, 3);
lean_inc(x_73);
lean_dec(x_29);
lean_inc(x_70);
x_74 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_78 = l_Lean_MessageData_ofExpr(x_75);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_77);
lean_ctor_set(x_30, 0, x_79);
x_80 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_34, x_30, x_8, x_9, x_10, x_11, x_76);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_13 = x_70;
x_14 = x_71;
x_15 = x_72;
x_16 = x_73;
x_17 = x_81;
goto block_20;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_free_object(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_74, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_84 = x_74;
} else {
 lean_dec_ref(x_74);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_30);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_88 = x_68;
} else {
 lean_dec_ref(x_68);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_30, 1);
lean_inc(x_90);
lean_dec(x_30);
x_91 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
x_92 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_91, x_10, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_ctor_get(x_29, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_29, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_29, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_29, 3);
lean_inc(x_99);
lean_dec(x_29);
x_13 = x_96;
x_14 = x_97;
x_15 = x_98;
x_16 = x_99;
x_17 = x_95;
goto block_20;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_101 = x_92;
} else {
 lean_dec_ref(x_92);
 x_101 = lean_box(0);
}
x_102 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_29, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_29, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_29, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_29, 3);
lean_inc(x_107);
lean_dec(x_29);
lean_inc(x_104);
x_108 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_103);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_112 = l_Lean_MessageData_ofExpr(x_109);
if (lean_is_scalar(x_101)) {
 x_113 = lean_alloc_ctor(7, 2, 0);
} else {
 x_113 = x_101;
 lean_ctor_set_tag(x_113, 7);
}
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
x_115 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_91, x_114, x_8, x_9, x_10, x_11, x_110);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_13 = x_104;
x_14 = x_105;
x_15 = x_106;
x_16 = x_107;
x_17 = x_116;
goto block_20;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_108, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_108, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_119 = x_108;
} else {
 lean_dec_ref(x_108);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_101);
lean_dec(x_29);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
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
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_21);
if (x_127 == 0)
{
return x_21;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_21, 0);
x_129 = lean_ctor_get(x_21, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_21);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_1);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_16);
lean_ctor_set(x_18, 5, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simplified", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; uint8_t x_94; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_4, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_94 = lean_unbox(x_14);
lean_dec(x_14);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_17, 0);
lean_inc(x_95);
x_24 = x_95;
goto block_93;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_inc(x_17);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_17);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_17);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_15);
return x_98;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
block_93:
{
lean_object* x_25; 
x_25 = l_Lean_Grind_CommRing_Poly_findSimp_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1;
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_28, x_10, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_19 = x_32;
goto block_23;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
x_36 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_17);
x_38 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1_spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_42 = l_Lean_MessageData_ofExpr(x_39);
x_43 = l_Lean_indentD(x_42);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_43);
lean_ctor_set(x_29, 0, x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_28, x_45, x_8, x_9, x_10, x_11, x_40);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_19 = x_47;
goto block_23;
}
else
{
uint8_t x_48; 
lean_free_object(x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
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
lean_free_object(x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_17);
x_59 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1_spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_63 = l_Lean_MessageData_ofExpr(x_60);
x_64 = l_Lean_indentD(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_28, x_67, x_8, x_9, x_10, x_11, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_19 = x_69;
goto block_23;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_76 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_18);
lean_dec(x_16);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_dec(x_25);
x_79 = lean_ctor_get(x_26, 0);
lean_inc(x_79);
lean_dec(x_26);
x_80 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith(x_17, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_81);
x_2 = x_83;
x_12 = x_82;
goto _start;
}
else
{
uint8_t x_85; 
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_25);
if (x_89 == 0)
{
return x_25;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_25, 0);
x_91 = lean_ctor_get(x_25, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_25);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; uint8_t x_94; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_4, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_94 = lean_unbox(x_14);
lean_dec(x_14);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_17, 0);
lean_inc(x_95);
x_24 = x_95;
goto block_93;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_inc(x_17);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_17);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_17);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_15);
return x_98;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
block_93:
{
lean_object* x_25; 
x_25 = l_Lean_Grind_CommRing_Poly_findSimp_x3f(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1;
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_28, x_10, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_19 = x_32;
goto block_23;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
x_36 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_17);
x_38 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1_spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_42 = l_Lean_MessageData_ofExpr(x_39);
x_43 = l_Lean_indentD(x_42);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_43);
lean_ctor_set(x_29, 0, x_41);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_28, x_45, x_8, x_9, x_10, x_11, x_40);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_19 = x_47;
goto block_23;
}
else
{
uint8_t x_48; 
lean_free_object(x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
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
lean_free_object(x_29);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_dec(x_29);
x_57 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_17);
x_59 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1_spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_63 = l_Lean_MessageData_ofExpr(x_60);
x_64 = l_Lean_indentD(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_28, x_67, x_8, x_9, x_10, x_11, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_19 = x_69;
goto block_23;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_70 = lean_ctor_get(x_59, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_59, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_72 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_74 = lean_ctor_get(x_57, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_76 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_18);
lean_dec(x_16);
x_78 = lean_ctor_get(x_25, 1);
lean_inc(x_78);
lean_dec(x_25);
x_79 = lean_ctor_get(x_26, 0);
lean_inc(x_79);
lean_dec(x_26);
x_80 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith(x_17, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_81);
x_84 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0(x_1, x_83, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_82);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
return x_80;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_80, 0);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_80);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_25);
if (x_89 == 0)
{
return x_25;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_25, 0);
x_91 = lean_ctor_get(x_25, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_25);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___Lean_Grind_CommRing_Expr_toPolyM_spec__0(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = l_Lean_Grind_CommRing_Poly_simp_x3f(x_17, x_20, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_13);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(x_4, x_16);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_29, x_10, x_27);
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
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_44; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
x_39 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_1);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_2);
lean_inc(x_35);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 1, x_39);
x_44 = lean_unbox(x_31);
lean_dec(x_31);
if (x_44 == 0)
{
lean_dec(x_35);
lean_free_object(x_25);
x_40 = x_32;
goto block_43;
}
else
{
lean_object* x_45; 
x_45 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_51 = l_Lean_MessageData_ofExpr(x_48);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_51);
lean_ctor_set(x_25, 0, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_25);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_52, x_8, x_9, x_10, x_11, x_49);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_40 = x_54;
goto block_43;
}
else
{
uint8_t x_55; 
lean_dec(x_23);
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_24);
x_55 = !lean_is_exclusive(x_47);
if (x_55 == 0)
{
return x_47;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_47, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_23);
lean_dec(x_35);
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_24);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
return x_45;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_45, 0);
x_61 = lean_ctor_get(x_45, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_45);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
if (lean_is_scalar(x_24)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_24;
}
lean_ctor_set(x_41, 0, x_23);
if (lean_is_scalar(x_33)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_33;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_73; 
x_63 = lean_ctor_get(x_23, 0);
x_64 = lean_ctor_get(x_23, 1);
x_65 = lean_ctor_get(x_23, 2);
x_66 = lean_ctor_get(x_23, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_23);
x_67 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_1);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_2);
lean_inc(x_63);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_18);
lean_ctor_set(x_68, 3, x_19);
x_73 = lean_unbox(x_31);
lean_dec(x_31);
if (x_73 == 0)
{
lean_dec(x_63);
lean_free_object(x_25);
x_69 = x_32;
goto block_72;
}
else
{
lean_object* x_74; 
x_74 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_80 = l_Lean_MessageData_ofExpr(x_77);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_80);
lean_ctor_set(x_25, 0, x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_25);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_81, x_8, x_9, x_10, x_11, x_78);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_69 = x_83;
goto block_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_68);
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_24);
x_84 = lean_ctor_get(x_76, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_86 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_68);
lean_dec(x_63);
lean_dec(x_33);
lean_free_object(x_25);
lean_dec(x_24);
x_88 = lean_ctor_get(x_74, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_90 = x_74;
} else {
 lean_dec_ref(x_74);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
block_72:
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_24)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_24;
}
lean_ctor_set(x_70, 0, x_68);
if (lean_is_scalar(x_33)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_33;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_109; 
x_92 = lean_ctor_get(x_25, 1);
lean_inc(x_92);
lean_dec(x_25);
x_93 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
x_94 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_93, x_10, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_23, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_23, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_23, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_23, 3);
lean_inc(x_101);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_102 = x_23;
} else {
 lean_dec_ref(x_23);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_1);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set(x_103, 4, x_2);
lean_inc(x_98);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 4, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_18);
lean_ctor_set(x_104, 3, x_19);
x_109 = lean_unbox(x_95);
lean_dec(x_95);
if (x_109 == 0)
{
lean_dec(x_98);
x_105 = x_96;
goto block_108;
}
else
{
lean_object* x_110; 
x_110 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_116 = l_Lean_MessageData_ofExpr(x_113);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
x_119 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_93, x_118, x_8, x_9, x_10, x_11, x_114);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_105 = x_120;
goto block_108;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_97);
lean_dec(x_24);
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_123 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_104);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_24);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_110, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_127 = x_110;
} else {
 lean_dec_ref(x_110);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
block_108:
{
lean_object* x_106; lean_object* x_107; 
if (lean_is_scalar(x_24)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_24;
}
lean_ctor_set(x_106, 0, x_104);
if (lean_is_scalar(x_97)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_97;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_13, 0);
x_130 = lean_ctor_get(x_13, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_13);
x_131 = lean_ctor_get(x_1, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_1, 2);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_2, 0);
lean_inc(x_134);
x_135 = l_Lean_Grind_CommRing_Poly_simp_x3f(x_131, x_134, x_129);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_159; 
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
x_140 = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(x_4, x_130);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3;
x_144 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_143, x_10, x_141);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_138, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_138, 3);
lean_inc(x_151);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 x_152 = x_138;
} else {
 lean_dec_ref(x_138);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_1);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set(x_153, 4, x_2);
lean_inc(x_148);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 4, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_154, 2, x_132);
lean_ctor_set(x_154, 3, x_133);
x_159 = lean_unbox(x_145);
lean_dec(x_145);
if (x_159 == 0)
{
lean_dec(x_148);
lean_dec(x_142);
x_155 = x_146;
goto block_158;
}
else
{
lean_object* x_160; 
x_160 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_146);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_148, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_166 = l_Lean_MessageData_ofExpr(x_163);
if (lean_is_scalar(x_142)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_142;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
x_169 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_143, x_168, x_8, x_9, x_10, x_11, x_164);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_155 = x_170;
goto block_158;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_154);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_139);
x_171 = lean_ctor_get(x_162, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_162, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_173 = x_162;
} else {
 lean_dec_ref(x_162);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_154);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_139);
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_177 = x_160;
} else {
 lean_dec_ref(x_160);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
block_158:
{
lean_object* x_156; lean_object* x_157; 
if (lean_is_scalar(x_139)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_139;
}
lean_ctor_set(x_156, 0, x_154);
if (lean_is_scalar(x_147)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_147;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_2);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_13);
if (x_179 == 0)
{
return x_13;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_13, 0);
x_181 = lean_ctor_get(x_13, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_13);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_1 = x_20;
x_12 = x_19;
goto _start;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_4, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_24 = lean_unbox(x_14);
lean_dec(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = l_Lean_Grind_CommRing_Poly_findSimp_x3f(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1;
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_29, x_10, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_19 = x_33;
goto block_23;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_17);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_43 = l_Lean_MessageData_ofExpr(x_40);
x_44 = l_Lean_indentD(x_43);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_44);
lean_ctor_set(x_30, 0, x_42);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_46, x_8, x_9, x_10, x_11, x_41);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_19 = x_48;
goto block_23;
}
else
{
uint8_t x_49; 
lean_free_object(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
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
lean_free_object(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_30, 1);
lean_inc(x_57);
lean_dec(x_30);
x_58 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_17);
x_60 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_64 = l_Lean_MessageData_ofExpr(x_61);
x_65 = l_Lean_indentD(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_68, x_8, x_9, x_10, x_11, x_62);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_19 = x_70;
goto block_23;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_75 = lean_ctor_get(x_58, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_77 = x_58;
} else {
 lean_dec_ref(x_58);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_18);
lean_dec(x_16);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_dec(x_26);
x_80 = lean_ctor_get(x_27, 0);
lean_inc(x_80);
lean_dec(x_27);
x_81 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith(x_17, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_82);
x_2 = x_84;
x_12 = x_83;
goto _start;
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_26);
if (x_90 == 0)
{
return x_26;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_26, 0);
x_92 = lean_ctor_get(x_26, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_inc(x_17);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_17);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_17);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_15);
return x_96;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_13 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_4, x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_18 = x_2;
} else {
 lean_dec_ref(x_2);
 x_18 = lean_box(0);
}
x_24 = lean_unbox(x_14);
lean_dec(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = l_Lean_Grind_CommRing_Poly_findSimp_x3f(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1;
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_29, x_10, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_19 = x_33;
goto block_23;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_17);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_43 = l_Lean_MessageData_ofExpr(x_40);
x_44 = l_Lean_indentD(x_43);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_44);
lean_ctor_set(x_30, 0, x_42);
x_45 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_30);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_46, x_8, x_9, x_10, x_11, x_41);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_19 = x_48;
goto block_23;
}
else
{
uint8_t x_49; 
lean_free_object(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_39);
if (x_49 == 0)
{
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
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
lean_free_object(x_30);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
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
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_30, 1);
lean_inc(x_57);
lean_dec(x_30);
x_58 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_17);
x_60 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3;
x_64 = l_Lean_MessageData_ofExpr(x_61);
x_65 = l_Lean_indentD(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_68, x_8, x_9, x_10, x_11, x_62);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_19 = x_70;
goto block_23;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_73 = x_60;
} else {
 lean_dec_ref(x_60);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_75 = lean_ctor_get(x_58, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_58, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_77 = x_58;
} else {
 lean_dec_ref(x_58);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_18);
lean_dec(x_16);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_dec(x_26);
x_80 = lean_ctor_get(x_27, 0);
lean_inc(x_80);
lean_dec(x_27);
x_81 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWith(x_17, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_1);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0(x_1, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_83);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_81);
if (x_86 == 0)
{
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 0);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_81);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_26);
if (x_90 == 0)
{
return x_26;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_26, 0);
x_92 = lean_ctor_get(x_26, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
lean_inc(x_17);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_17);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_17);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_15);
return x_96;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
if (lean_is_scalar(x_18)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_18;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_16, 0);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discard", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_19 = lean_int_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_Arith_CommRing_hasChar(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_ctor_get(x_20, 0);
lean_dec(x_25);
x_26 = lean_nat_abs(x_17);
lean_dec(x_17);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
x_30 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_29, x_9, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_20);
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
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_12 = x_33;
goto block_15;
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 1);
x_36 = lean_ctor_get(x_30, 0);
lean_dec(x_36);
x_37 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_43 = l_Lean_MessageData_ofExpr(x_40);
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_43);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_42);
lean_ctor_set(x_20, 0, x_30);
x_44 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_20, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_12 = x_45;
goto block_15;
}
else
{
uint8_t x_46; 
lean_free_object(x_30);
lean_free_object(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
else
{
uint8_t x_50; 
lean_free_object(x_30);
lean_free_object(x_20);
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
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_dec(x_30);
x_55 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_61 = l_Lean_MessageData_ofExpr(x_58);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_60);
lean_ctor_set(x_20, 0, x_62);
x_63 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_29, x_20, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_12 = x_64;
goto block_15;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_free_object(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_67 = x_57;
} else {
 lean_dec_ref(x_57);
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
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_20);
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
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_71 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
}
else
{
lean_object* x_73; 
lean_free_object(x_20);
x_73 = l_Lean_Meta_Grind_Arith_CommRing_isField(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_77 = lean_ctor_get(x_73, 1);
x_78 = lean_ctor_get(x_73, 0);
lean_dec(x_78);
x_79 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
x_80 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_79, x_9, x_77);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_free_object(x_73);
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
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_12 = x_83;
goto block_15;
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
x_86 = lean_ctor_get(x_80, 0);
lean_dec(x_86);
x_87 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_88);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_93 = l_Lean_MessageData_ofExpr(x_90);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_93);
lean_ctor_set(x_80, 0, x_92);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_92);
lean_ctor_set(x_73, 0, x_80);
x_94 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_79, x_73, x_7, x_8, x_9, x_10, x_91);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_12 = x_95;
goto block_15;
}
else
{
uint8_t x_96; 
lean_free_object(x_80);
lean_free_object(x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_96 = !lean_is_exclusive(x_89);
if (x_96 == 0)
{
return x_89;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_89, 0);
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_89);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_80);
lean_free_object(x_73);
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
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
return x_87;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_87, 0);
x_102 = lean_ctor_get(x_87, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_87);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_80, 1);
lean_inc(x_104);
lean_dec(x_80);
x_105 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_111 = l_Lean_MessageData_ofExpr(x_108);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_110);
lean_ctor_set(x_73, 0, x_112);
x_113 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_79, x_73, x_7, x_8, x_9, x_10, x_109);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_12 = x_114;
goto block_15;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_73);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_115 = lean_ctor_get(x_107, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_107, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_117 = x_107;
} else {
 lean_dec_ref(x_107);
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
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_free_object(x_73);
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
x_119 = lean_ctor_get(x_105, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_105, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_121 = x_105;
} else {
 lean_dec_ref(x_105);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_73, 1);
lean_inc(x_123);
lean_dec(x_73);
x_124 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
x_125 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_124, x_9, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
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
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_12 = x_128;
goto block_15;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_137 = l_Lean_MessageData_ofExpr(x_134);
if (lean_is_scalar(x_130)) {
 x_138 = lean_alloc_ctor(7, 2, 0);
} else {
 x_138 = x_130;
 lean_ctor_set_tag(x_138, 7);
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
x_140 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_124, x_139, x_7, x_8, x_9, x_10, x_135);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_12 = x_141;
goto block_15;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_130);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_142 = lean_ctor_get(x_133, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_133, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_144 = x_133;
} else {
 lean_dec_ref(x_133);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_130);
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
x_146 = lean_ctor_get(x_131, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_131, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_148 = x_131;
} else {
 lean_dec_ref(x_131);
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
}
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_73, 1);
lean_inc(x_150);
lean_dec(x_73);
x_151 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_12 = x_152;
goto block_15;
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
return x_151;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_151, 0);
x_155 = lean_ctor_get(x_151, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_151);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
else
{
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
return x_73;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_20, 1);
lean_inc(x_157);
lean_dec(x_20);
x_158 = lean_nat_abs(x_17);
lean_dec(x_17);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_dec_eq(x_158, x_159);
lean_dec(x_158);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_161 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
x_162 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_161, x_9, x_157);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; 
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
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_12 = x_165;
goto block_15;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_169);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_174 = l_Lean_MessageData_ofExpr(x_171);
if (lean_is_scalar(x_167)) {
 x_175 = lean_alloc_ctor(7, 2, 0);
} else {
 x_175 = x_167;
 lean_ctor_set_tag(x_175, 7);
}
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
x_177 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_161, x_176, x_7, x_8, x_9, x_10, x_172);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_12 = x_178;
goto block_15;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_167);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_167);
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
x_183 = lean_ctor_get(x_168, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_168, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_185 = x_168;
} else {
 lean_dec_ref(x_168);
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
}
else
{
lean_object* x_187; 
x_187 = l_Lean_Meta_Grind_Arith_CommRing_isField(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_157);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
 x_191 = lean_box(0);
}
x_192 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3;
x_193 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_192, x_9, x_190);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
lean_dec(x_194);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_191);
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
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_12 = x_196;
goto block_15;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
x_199 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_200);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_205 = l_Lean_MessageData_ofExpr(x_202);
if (lean_is_scalar(x_198)) {
 x_206 = lean_alloc_ctor(7, 2, 0);
} else {
 x_206 = x_198;
 lean_ctor_set_tag(x_206, 7);
}
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
if (lean_is_scalar(x_191)) {
 x_207 = lean_alloc_ctor(7, 2, 0);
} else {
 x_207 = x_191;
 lean_ctor_set_tag(x_207, 7);
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
x_208 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_192, x_207, x_7, x_8, x_9, x_10, x_203);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_12 = x_209;
goto block_15;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_198);
lean_dec(x_191);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_210 = lean_ctor_get(x_201, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_201, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_212 = x_201;
} else {
 lean_dec_ref(x_201);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_198);
lean_dec(x_191);
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
x_214 = lean_ctor_get(x_199, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_216 = x_199;
} else {
 lean_dec_ref(x_199);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_187, 1);
lean_inc(x_218);
lean_dec(x_187);
x_219 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_12 = x_220;
goto block_15;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
}
else
{
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
return x_187;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_17);
x_225 = lean_ctor_get(x_20, 1);
lean_inc(x_225);
lean_dec(x_20);
x_226 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_12 = x_227;
goto block_15;
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_226);
if (x_228 == 0)
{
return x_226;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_226, 0);
x_230 = lean_ctor_get(x_226, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_226);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
}
else
{
lean_dec(x_17);
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
return x_20;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
lean_dec(x_17);
x_232 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5;
x_233 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_232, x_9, x_11);
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; 
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
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_12 = x_236;
goto block_15;
}
else
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_233);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_233, 1);
x_239 = lean_ctor_get(x_233, 0);
lean_dec(x_239);
x_240 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_238);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_241);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_246 = l_Lean_MessageData_ofExpr(x_243);
lean_ctor_set_tag(x_233, 7);
lean_ctor_set(x_233, 1, x_246);
lean_ctor_set(x_233, 0, x_245);
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_233);
lean_ctor_set(x_247, 1, x_245);
x_248 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_232, x_247, x_7, x_8, x_9, x_10, x_244);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_12 = x_249;
goto block_15;
}
else
{
uint8_t x_250; 
lean_free_object(x_233);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_250 = !lean_is_exclusive(x_242);
if (x_250 == 0)
{
return x_242;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_242, 0);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_242);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_free_object(x_233);
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
x_254 = !lean_is_exclusive(x_240);
if (x_254 == 0)
{
return x_240;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_240, 0);
x_256 = lean_ctor_get(x_240, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_240);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_233, 1);
lean_inc(x_258);
lean_dec(x_233);
x_259 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_260);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_265 = l_Lean_MessageData_ofExpr(x_262);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_264);
x_268 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_232, x_267, x_7, x_8, x_9, x_10, x_263);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec(x_268);
x_12 = x_269;
goto block_15;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_270 = lean_ctor_get(x_261, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_261, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_272 = x_261;
} else {
 lean_dec_ref(x_261);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
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
x_274 = lean_ctor_get(x_259, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_259, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_276 = x_259;
} else {
 lean_dec_ref(x_259);
 x_276 = lean_box(0);
}
if (lean_is_scalar(x_276)) {
 x_277 = lean_alloc_ctor(1, 2, 0);
} else {
 x_277 = x_276;
}
lean_ctor_set(x_277, 0, x_274);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_16);
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
x_278 = lean_box(0);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_11);
return x_279;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyAndCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
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
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_15, 0, x_26);
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_12);
if (x_34 == 0)
{
return x_12;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_12, 0);
x_36 = lean_ctor_get(x_12, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_12);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_Grind_CommRing_Poly_lm(x_6);
lean_dec(x_6);
x_9 = l_Lean_Grind_CommRing_Poly_lm(x_7);
lean_dec(x_7);
x_10 = l_Lean_Grind_CommRing_Mon_grevlex(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_box(2);
x_12 = lean_unbox(x_11);
x_13 = l_instDecidableEqOrdering(x_10, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_2, 0);
lean_dec(x_16);
x_17 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(x_1, x_5);
lean_ctor_set(x_2, 1, x_17);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(x_1, x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("basis", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1;
x_124 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_123, x_9, x_11);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_48 = x_2;
x_49 = x_3;
x_50 = x_127;
goto block_122;
}
else
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_124, 1);
x_130 = lean_ctor_get(x_124, 0);
lean_dec(x_130);
lean_inc(x_1);
x_131 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_135 = l_Lean_MessageData_ofExpr(x_132);
lean_ctor_set_tag(x_124, 7);
lean_ctor_set(x_124, 1, x_135);
lean_ctor_set(x_124, 0, x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_124);
lean_ctor_set(x_136, 1, x_134);
x_137 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_123, x_136, x_7, x_8, x_9, x_10, x_133);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_48 = x_2;
x_49 = x_3;
x_50 = x_138;
goto block_122;
}
else
{
uint8_t x_139; 
lean_free_object(x_124);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_131);
if (x_139 == 0)
{
return x_131;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_131, 0);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_131);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_124, 1);
lean_inc(x_143);
lean_dec(x_124);
lean_inc(x_1);
x_144 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_148 = l_Lean_MessageData_ofExpr(x_145);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_123, x_150, x_7, x_8, x_9, x_10, x_146);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_48 = x_2;
x_49 = x_3;
x_50 = x_152;
goto block_122;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_1);
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_144, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_155 = x_144;
} else {
 lean_dec_ref(x_144);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_14);
lean_ctor_set(x_37, 3, x_15);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_29);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_22);
x_39 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_19);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set(x_39, 3, x_30);
lean_ctor_set(x_39, 4, x_24);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_26);
lean_ctor_set(x_39, 8, x_16);
lean_ctor_set(x_39, 9, x_17);
lean_ctor_set(x_39, 10, x_33);
lean_ctor_set(x_39, 11, x_28);
lean_ctor_set(x_39, 12, x_18);
lean_ctor_set(x_39, 13, x_12);
lean_ctor_set(x_39, 14, x_38);
lean_ctor_set(x_39, 15, x_27);
lean_ctor_set_uint8(x_39, sizeof(void*)*16, x_23);
x_40 = lean_st_ref_set(x_25, x_39, x_32);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_122:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_51 = lean_st_ref_take(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 14);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 7);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_52, sizeof(void*)*16);
x_66 = lean_ctor_get(x_52, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 10);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 11);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 12);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 13);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 15);
lean_inc(x_72);
lean_dec(x_52);
x_73 = lean_ctor_get(x_53, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 3);
lean_inc(x_75);
lean_dec(x_53);
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_54, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_54, 3);
lean_inc(x_79);
lean_dec(x_54);
x_80 = lean_array_get_size(x_76);
x_81 = lean_nat_dec_lt(x_56, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_dec(x_1);
x_12 = x_71;
x_13 = x_77;
x_14 = x_78;
x_15 = x_79;
x_16 = x_66;
x_17 = x_67;
x_18 = x_70;
x_19 = x_58;
x_20 = x_59;
x_21 = x_73;
x_22 = x_75;
x_23 = x_65;
x_24 = x_61;
x_25 = x_49;
x_26 = x_64;
x_27 = x_72;
x_28 = x_69;
x_29 = x_74;
x_30 = x_60;
x_31 = x_63;
x_32 = x_55;
x_33 = x_68;
x_34 = x_57;
x_35 = x_62;
x_36 = x_76;
goto block_47;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_array_fget(x_76, x_56);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 25);
x_85 = lean_box(0);
x_86 = lean_array_fset(x_76, x_56, x_85);
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(x_1, x_84);
lean_ctor_set(x_82, 25, x_87);
lean_ctor_set_uint8(x_82, sizeof(void*)*28, x_81);
x_88 = lean_array_fset(x_86, x_56, x_82);
x_12 = x_71;
x_13 = x_77;
x_14 = x_78;
x_15 = x_79;
x_16 = x_66;
x_17 = x_67;
x_18 = x_70;
x_19 = x_58;
x_20 = x_59;
x_21 = x_73;
x_22 = x_75;
x_23 = x_65;
x_24 = x_61;
x_25 = x_49;
x_26 = x_64;
x_27 = x_72;
x_28 = x_69;
x_29 = x_74;
x_30 = x_60;
x_31 = x_63;
x_32 = x_55;
x_33 = x_68;
x_34 = x_57;
x_35 = x_62;
x_36 = x_88;
goto block_47;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 3);
x_93 = lean_ctor_get(x_82, 4);
x_94 = lean_ctor_get(x_82, 5);
x_95 = lean_ctor_get(x_82, 6);
x_96 = lean_ctor_get(x_82, 7);
x_97 = lean_ctor_get(x_82, 8);
x_98 = lean_ctor_get(x_82, 9);
x_99 = lean_ctor_get(x_82, 10);
x_100 = lean_ctor_get(x_82, 11);
x_101 = lean_ctor_get(x_82, 12);
x_102 = lean_ctor_get(x_82, 13);
x_103 = lean_ctor_get(x_82, 14);
x_104 = lean_ctor_get(x_82, 15);
x_105 = lean_ctor_get(x_82, 16);
x_106 = lean_ctor_get(x_82, 17);
x_107 = lean_ctor_get(x_82, 18);
x_108 = lean_ctor_get(x_82, 19);
x_109 = lean_ctor_get(x_82, 20);
x_110 = lean_ctor_get(x_82, 21);
x_111 = lean_ctor_get(x_82, 22);
x_112 = lean_ctor_get(x_82, 23);
x_113 = lean_ctor_get(x_82, 24);
x_114 = lean_ctor_get(x_82, 25);
x_115 = lean_ctor_get(x_82, 26);
x_116 = lean_ctor_get(x_82, 27);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_117 = lean_box(0);
x_118 = lean_array_fset(x_76, x_56, x_117);
x_119 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_addSorted(x_1, x_114);
x_120 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_120, 0, x_89);
lean_ctor_set(x_120, 1, x_90);
lean_ctor_set(x_120, 2, x_91);
lean_ctor_set(x_120, 3, x_92);
lean_ctor_set(x_120, 4, x_93);
lean_ctor_set(x_120, 5, x_94);
lean_ctor_set(x_120, 6, x_95);
lean_ctor_set(x_120, 7, x_96);
lean_ctor_set(x_120, 8, x_97);
lean_ctor_set(x_120, 9, x_98);
lean_ctor_set(x_120, 10, x_99);
lean_ctor_set(x_120, 11, x_100);
lean_ctor_set(x_120, 12, x_101);
lean_ctor_set(x_120, 13, x_102);
lean_ctor_set(x_120, 14, x_103);
lean_ctor_set(x_120, 15, x_104);
lean_ctor_set(x_120, 16, x_105);
lean_ctor_set(x_120, 17, x_106);
lean_ctor_set(x_120, 18, x_107);
lean_ctor_set(x_120, 19, x_108);
lean_ctor_set(x_120, 20, x_109);
lean_ctor_set(x_120, 21, x_110);
lean_ctor_set(x_120, 22, x_111);
lean_ctor_set(x_120, 23, x_112);
lean_ctor_set(x_120, 24, x_113);
lean_ctor_set(x_120, 25, x_119);
lean_ctor_set(x_120, 26, x_115);
lean_ctor_set(x_120, 27, x_116);
lean_ctor_set_uint8(x_120, sizeof(void*)*28, x_81);
x_121 = lean_array_fset(x_118, x_56, x_120);
x_12 = x_71;
x_13 = x_77;
x_14 = x_78;
x_15 = x_79;
x_16 = x_66;
x_17 = x_67;
x_18 = x_70;
x_19 = x_58;
x_20 = x_59;
x_21 = x_73;
x_22 = x_75;
x_23 = x_65;
x_24 = x_61;
x_25 = x_49;
x_26 = x_64;
x_27 = x_72;
x_28 = x_69;
x_29 = x_74;
x_30 = x_60;
x_31 = x_63;
x_32 = x_55;
x_33 = x_68;
x_34 = x_57;
x_35 = x_62;
x_36 = x_121;
goto block_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("queue", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_124 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_3, x_5, x_11);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1;
x_129 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_128, x_9, x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_48 = x_2;
x_49 = x_3;
x_50 = x_132;
goto block_123;
}
else
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_129);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_129, 1);
x_135 = lean_ctor_get(x_129, 0);
lean_dec(x_135);
x_136 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 1);
x_139 = lean_ctor_get(x_136, 0);
lean_dec(x_139);
lean_inc(x_1);
x_140 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_144 = l_Lean_MessageData_ofExpr(x_141);
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_144);
lean_ctor_set(x_136, 0, x_143);
lean_ctor_set_tag(x_129, 7);
lean_ctor_set(x_129, 1, x_143);
lean_ctor_set(x_129, 0, x_136);
x_145 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_128, x_129, x_7, x_8, x_9, x_10, x_142);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_48 = x_2;
x_49 = x_3;
x_50 = x_146;
goto block_123;
}
else
{
uint8_t x_147; 
lean_free_object(x_136);
lean_free_object(x_129);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_140);
if (x_147 == 0)
{
return x_140;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_140, 0);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_140);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_136, 1);
lean_inc(x_151);
lean_dec(x_136);
lean_inc(x_1);
x_152 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_156 = l_Lean_MessageData_ofExpr(x_153);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set_tag(x_129, 7);
lean_ctor_set(x_129, 1, x_155);
lean_ctor_set(x_129, 0, x_157);
x_158 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_128, x_129, x_7, x_8, x_9, x_10, x_154);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_48 = x_2;
x_49 = x_3;
x_50 = x_159;
goto block_123;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_129);
lean_dec(x_1);
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_162 = x_152;
} else {
 lean_dec_ref(x_152);
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
lean_free_object(x_129);
lean_dec(x_1);
return x_136;
}
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_129, 1);
lean_inc(x_164);
lean_dec(x_129);
x_165 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
lean_inc(x_1);
x_168 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_172 = l_Lean_MessageData_ofExpr(x_169);
if (lean_is_scalar(x_167)) {
 x_173 = lean_alloc_ctor(7, 2, 0);
} else {
 x_173 = x_167;
 lean_ctor_set_tag(x_173, 7);
}
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
x_175 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_128, x_174, x_7, x_8, x_9, x_10, x_170);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_48 = x_2;
x_49 = x_3;
x_50 = x_176;
goto block_123;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_167);
lean_dec(x_1);
x_177 = lean_ctor_get(x_168, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_168, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_179 = x_168;
} else {
 lean_dec_ref(x_168);
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
lean_dec(x_1);
return x_165;
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_124);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_124, 0);
lean_dec(x_182);
x_183 = lean_box(0);
lean_ctor_set(x_124, 0, x_183);
return x_124;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_124, 1);
lean_inc(x_184);
lean_dec(x_124);
x_185 = lean_box(0);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_27);
lean_ctor_set(x_37, 3, x_28);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_15);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_20);
x_39 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_14);
lean_ctor_set(x_39, 2, x_21);
lean_ctor_set(x_39, 3, x_19);
lean_ctor_set(x_39, 4, x_24);
lean_ctor_set(x_39, 5, x_22);
lean_ctor_set(x_39, 6, x_16);
lean_ctor_set(x_39, 7, x_29);
lean_ctor_set(x_39, 8, x_34);
lean_ctor_set(x_39, 9, x_31);
lean_ctor_set(x_39, 10, x_32);
lean_ctor_set(x_39, 11, x_23);
lean_ctor_set(x_39, 12, x_30);
lean_ctor_set(x_39, 13, x_18);
lean_ctor_set(x_39, 14, x_38);
lean_ctor_set(x_39, 15, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*16, x_12);
x_40 = lean_st_ref_set(x_25, x_39, x_17);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_123:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_51 = lean_st_ref_take(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 14);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 7);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_52, sizeof(void*)*16);
x_66 = lean_ctor_get(x_52, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 10);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 11);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 12);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 13);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 15);
lean_inc(x_72);
lean_dec(x_52);
x_73 = lean_ctor_get(x_53, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 3);
lean_inc(x_75);
lean_dec(x_53);
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_54, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_54, 3);
lean_inc(x_79);
lean_dec(x_54);
x_80 = lean_array_get_size(x_76);
x_81 = lean_nat_dec_lt(x_56, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_dec(x_1);
x_12 = x_65;
x_13 = x_57;
x_14 = x_58;
x_15 = x_74;
x_16 = x_63;
x_17 = x_55;
x_18 = x_71;
x_19 = x_60;
x_20 = x_75;
x_21 = x_59;
x_22 = x_62;
x_23 = x_69;
x_24 = x_61;
x_25 = x_49;
x_26 = x_77;
x_27 = x_78;
x_28 = x_79;
x_29 = x_64;
x_30 = x_70;
x_31 = x_67;
x_32 = x_68;
x_33 = x_72;
x_34 = x_66;
x_35 = x_73;
x_36 = x_76;
goto block_47;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_array_fget(x_76, x_56);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 24);
x_85 = lean_box(0);
x_86 = lean_array_fset(x_76, x_56, x_85);
x_87 = l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0___redArg(x_84, x_1, x_85);
lean_ctor_set(x_82, 24, x_87);
x_88 = lean_array_fset(x_86, x_56, x_82);
x_12 = x_65;
x_13 = x_57;
x_14 = x_58;
x_15 = x_74;
x_16 = x_63;
x_17 = x_55;
x_18 = x_71;
x_19 = x_60;
x_20 = x_75;
x_21 = x_59;
x_22 = x_62;
x_23 = x_69;
x_24 = x_61;
x_25 = x_49;
x_26 = x_77;
x_27 = x_78;
x_28 = x_79;
x_29 = x_64;
x_30 = x_70;
x_31 = x_67;
x_32 = x_68;
x_33 = x_72;
x_34 = x_66;
x_35 = x_73;
x_36 = x_88;
goto block_47;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 3);
x_93 = lean_ctor_get(x_82, 4);
x_94 = lean_ctor_get(x_82, 5);
x_95 = lean_ctor_get(x_82, 6);
x_96 = lean_ctor_get(x_82, 7);
x_97 = lean_ctor_get(x_82, 8);
x_98 = lean_ctor_get(x_82, 9);
x_99 = lean_ctor_get(x_82, 10);
x_100 = lean_ctor_get(x_82, 11);
x_101 = lean_ctor_get(x_82, 12);
x_102 = lean_ctor_get(x_82, 13);
x_103 = lean_ctor_get(x_82, 14);
x_104 = lean_ctor_get(x_82, 15);
x_105 = lean_ctor_get(x_82, 16);
x_106 = lean_ctor_get(x_82, 17);
x_107 = lean_ctor_get(x_82, 18);
x_108 = lean_ctor_get(x_82, 19);
x_109 = lean_ctor_get(x_82, 20);
x_110 = lean_ctor_get(x_82, 21);
x_111 = lean_ctor_get(x_82, 22);
x_112 = lean_ctor_get(x_82, 23);
x_113 = lean_ctor_get(x_82, 24);
x_114 = lean_ctor_get(x_82, 25);
x_115 = lean_ctor_get(x_82, 26);
x_116 = lean_ctor_get_uint8(x_82, sizeof(void*)*28);
x_117 = lean_ctor_get(x_82, 27);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_118 = lean_box(0);
x_119 = lean_array_fset(x_76, x_56, x_118);
x_120 = l_Lean_RBNode_insert___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue_spec__0___redArg(x_113, x_1, x_118);
x_121 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_121, 0, x_89);
lean_ctor_set(x_121, 1, x_90);
lean_ctor_set(x_121, 2, x_91);
lean_ctor_set(x_121, 3, x_92);
lean_ctor_set(x_121, 4, x_93);
lean_ctor_set(x_121, 5, x_94);
lean_ctor_set(x_121, 6, x_95);
lean_ctor_set(x_121, 7, x_96);
lean_ctor_set(x_121, 8, x_97);
lean_ctor_set(x_121, 9, x_98);
lean_ctor_set(x_121, 10, x_99);
lean_ctor_set(x_121, 11, x_100);
lean_ctor_set(x_121, 12, x_101);
lean_ctor_set(x_121, 13, x_102);
lean_ctor_set(x_121, 14, x_103);
lean_ctor_set(x_121, 15, x_104);
lean_ctor_set(x_121, 16, x_105);
lean_ctor_set(x_121, 17, x_106);
lean_ctor_set(x_121, 18, x_107);
lean_ctor_set(x_121, 19, x_108);
lean_ctor_set(x_121, 20, x_109);
lean_ctor_set(x_121, 21, x_110);
lean_ctor_set(x_121, 22, x_111);
lean_ctor_set(x_121, 23, x_112);
lean_ctor_set(x_121, 24, x_120);
lean_ctor_set(x_121, 25, x_114);
lean_ctor_set(x_121, 26, x_115);
lean_ctor_set(x_121, 27, x_117);
lean_ctor_set_uint8(x_121, sizeof(void*)*28, x_116);
x_122 = lean_array_fset(x_119, x_56, x_121);
x_12 = x_65;
x_13 = x_57;
x_14 = x_58;
x_15 = x_74;
x_16 = x_63;
x_17 = x_55;
x_18 = x_71;
x_19 = x_60;
x_20 = x_75;
x_21 = x_59;
x_22 = x_62;
x_23 = x_69;
x_24 = x_61;
x_25 = x_49;
x_26 = x_77;
x_27 = x_78;
x_28 = x_79;
x_29 = x_64;
x_30 = x_70;
x_31 = x_67;
x_32 = x_68;
x_33 = x_72;
x_34 = x_66;
x_35 = x_73;
x_36 = x_122;
goto block_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("superpose", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nwith: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nresult: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" = 0", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_dec(x_4);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_19;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = l_Lean_Grind_CommRing_Mon_sharesVar(x_2, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_free_object(x_4);
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_22;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = l_Lean_Grind_CommRing_Poly_spolM(x_27, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_58 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1;
x_59 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_58, x_13, x_30);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_4);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_62;
goto block_57;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 1);
x_65 = lean_ctor_get(x_59, 0);
lean_dec(x_65);
x_66 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_64);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
lean_inc(x_3);
x_70 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_17);
x_73 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_29, 0);
lean_inc(x_76);
x_77 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_76, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_81 = l_Lean_MessageData_ofExpr(x_71);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_81);
lean_ctor_set(x_66, 0, x_80);
x_82 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_82);
lean_ctor_set(x_59, 0, x_66);
x_83 = l_Lean_MessageData_ofExpr(x_74);
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_83);
lean_ctor_set(x_4, 0, x_59);
x_84 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_MessageData_ofExpr(x_78);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_58, x_89, x_11, x_12, x_13, x_14, x_79);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_91;
goto block_57;
}
else
{
uint8_t x_92; 
lean_dec(x_74);
lean_dec(x_71);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_77);
if (x_92 == 0)
{
return x_77;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_71);
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_73);
if (x_96 == 0)
{
return x_73;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_73, 0);
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_73);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_free_object(x_66);
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_70);
if (x_100 == 0)
{
return x_70;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_70, 0);
x_102 = lean_ctor_get(x_70, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_70);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_66, 1);
lean_inc(x_104);
lean_dec(x_66);
lean_inc(x_3);
x_105 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_17);
x_108 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_ctor_get(x_29, 0);
lean_inc(x_111);
x_112 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_111, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_116 = l_Lean_MessageData_ofExpr(x_106);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
lean_ctor_set_tag(x_59, 7);
lean_ctor_set(x_59, 1, x_118);
lean_ctor_set(x_59, 0, x_117);
x_119 = l_Lean_MessageData_ofExpr(x_109);
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_119);
lean_ctor_set(x_4, 0, x_59);
x_120 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_4);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_MessageData_ofExpr(x_113);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_58, x_125, x_11, x_12, x_13, x_14, x_114);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_127;
goto block_57;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_109);
lean_dec(x_106);
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_128 = lean_ctor_get(x_112, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_112, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_130 = x_112;
} else {
 lean_dec_ref(x_112);
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
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_106);
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_132 = lean_ctor_get(x_108, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_108, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_134 = x_108;
} else {
 lean_dec_ref(x_108);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_136 = lean_ctor_get(x_105, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_105, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_138 = x_105;
} else {
 lean_dec_ref(x_105);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
lean_free_object(x_59);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
return x_66;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_59, 1);
lean_inc(x_140);
lean_dec(x_59);
x_141 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
lean_inc(x_3);
x_144 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_17);
x_147 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_29, 0);
lean_inc(x_150);
x_151 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_150, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_149);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_155 = l_Lean_MessageData_ofExpr(x_145);
if (lean_is_scalar(x_143)) {
 x_156 = lean_alloc_ctor(7, 2, 0);
} else {
 x_156 = x_143;
 lean_ctor_set_tag(x_156, 7);
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_MessageData_ofExpr(x_148);
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_159);
lean_ctor_set(x_4, 0, x_158);
x_160 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_MessageData_ofExpr(x_152);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_58, x_165, x_11, x_12, x_13, x_14, x_153);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_167;
goto block_57;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_148);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_168 = lean_ctor_get(x_151, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_151, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_170 = x_151;
} else {
 lean_dec_ref(x_151);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_172 = lean_ctor_get(x_147, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_147, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_174 = x_147;
} else {
 lean_dec_ref(x_147);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_143);
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_176 = lean_ctor_get(x_144, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_144, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_178 = x_144;
} else {
 lean_dec_ref(x_144);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_dec(x_29);
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
return x_141;
}
}
}
block_57:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_29, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_29, 3);
lean_inc(x_44);
x_45 = lean_ctor_get(x_29, 4);
lean_inc(x_45);
lean_dec(x_29);
lean_inc(x_3);
x_46 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_3);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_17);
x_47 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_41, x_46, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_48, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_22;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_14 = x_51;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_15 = _tmp_14;
}
goto _start;
}
else
{
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
return x_50;
}
}
else
{
uint8_t x_53; 
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
uint8_t x_180; 
lean_free_object(x_4);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_180 = !lean_is_exclusive(x_28);
if (x_180 == 0)
{
return x_28;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_28, 0);
x_182 = lean_ctor_get(x_28, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_28);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_4, 1);
lean_inc(x_184);
lean_dec(x_4);
x_185 = lean_ctor_get(x_18, 1);
lean_inc(x_185);
x_186 = l_Lean_Grind_CommRing_Mon_sharesVar(x_2, x_185);
lean_dec(x_185);
if (x_186 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_184;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_3, 0);
lean_inc(x_188);
x_189 = l_Lean_Grind_CommRing_Poly_spolM(x_188, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_219 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1;
x_220 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_219, x_13, x_191);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_192 = x_6;
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_10;
x_197 = x_11;
x_198 = x_12;
x_199 = x_13;
x_200 = x_14;
x_201 = x_223;
goto block_218;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_225 = x_220;
} else {
 lean_dec_ref(x_220);
 x_225 = lean_box(0);
}
x_226 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_224);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_228 = x_226;
} else {
 lean_dec_ref(x_226);
 x_228 = lean_box(0);
}
lean_inc(x_3);
x_229 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_227);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_17);
x_232 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_ctor_get(x_190, 0);
lean_inc(x_235);
x_236 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_235, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_234);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_240 = l_Lean_MessageData_ofExpr(x_230);
if (lean_is_scalar(x_228)) {
 x_241 = lean_alloc_ctor(7, 2, 0);
} else {
 x_241 = x_228;
 lean_ctor_set_tag(x_241, 7);
}
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
if (lean_is_scalar(x_225)) {
 x_243 = lean_alloc_ctor(7, 2, 0);
} else {
 x_243 = x_225;
 lean_ctor_set_tag(x_243, 7);
}
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lean_MessageData_ofExpr(x_233);
x_245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_246 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_MessageData_ofExpr(x_237);
x_249 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_219, x_251, x_11, x_12, x_13, x_14, x_238);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_192 = x_6;
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_10;
x_197 = x_11;
x_198 = x_12;
x_199 = x_13;
x_200 = x_14;
x_201 = x_253;
goto block_218;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_233);
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_190);
lean_dec(x_184);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_254 = lean_ctor_get(x_236, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_236, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_256 = x_236;
} else {
 lean_dec_ref(x_236);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_190);
lean_dec(x_184);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_258 = lean_ctor_get(x_232, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_232, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_260 = x_232;
} else {
 lean_dec_ref(x_232);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_228);
lean_dec(x_225);
lean_dec(x_190);
lean_dec(x_184);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_262 = lean_ctor_get(x_229, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_229, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_264 = x_229;
} else {
 lean_dec_ref(x_229);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
else
{
lean_dec(x_225);
lean_dec(x_190);
lean_dec(x_184);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
return x_226;
}
}
block_218:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_190, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_190, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_190, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_190, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 4);
lean_inc(x_206);
lean_dec(x_190);
lean_inc(x_3);
x_207 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_207, 0, x_203);
lean_ctor_set(x_207, 1, x_204);
lean_ctor_set(x_207, 2, x_3);
lean_ctor_set(x_207, 3, x_205);
lean_ctor_set(x_207, 4, x_206);
lean_ctor_set(x_207, 5, x_17);
x_208 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_202, x_207, x_192, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_209, x_192, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
lean_inc(x_1);
{
lean_object* _tmp_3 = x_184;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_14 = x_212;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_15 = _tmp_14;
}
goto _start;
}
else
{
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_1);
return x_211;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_184);
lean_dec(x_3);
lean_dec(x_1);
x_214 = lean_ctor_get(x_208, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_208, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_216 = x_208;
} else {
 lean_dec_ref(x_208);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_184);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_189, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_189, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_268 = x_189;
} else {
 lean_dec_ref(x_189);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
lean_inc(x_1);
x_21 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_20, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_5, 1);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
x_26 = l_Lean_Grind_CommRing_Mon_sharesVar(x_2, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_5);
lean_dec(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_27 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_23, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = l_Lean_Grind_CommRing_Poly_spolM(x_28, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_59 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1;
x_60 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_59, x_14, x_31);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_free_object(x_5);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_15;
x_41 = x_63;
goto block_58;
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 1);
x_66 = lean_ctor_get(x_60, 0);
lean_dec(x_66);
x_67 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_65);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
lean_inc(x_3);
x_71 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_18);
x_74 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_30, 0);
lean_inc(x_77);
x_78 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_77, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_82 = l_Lean_MessageData_ofExpr(x_72);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_82);
lean_ctor_set(x_67, 0, x_81);
x_83 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
lean_ctor_set_tag(x_60, 7);
lean_ctor_set(x_60, 1, x_83);
lean_ctor_set(x_60, 0, x_67);
x_84 = l_Lean_MessageData_ofExpr(x_75);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_84);
lean_ctor_set(x_5, 0, x_60);
x_85 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_MessageData_ofExpr(x_79);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_59, x_90, x_12, x_13, x_14, x_15, x_80);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_15;
x_41 = x_92;
goto block_58;
}
else
{
uint8_t x_93; 
lean_dec(x_75);
lean_dec(x_72);
lean_free_object(x_67);
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_78);
if (x_93 == 0)
{
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_72);
lean_free_object(x_67);
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_74);
if (x_97 == 0)
{
return x_74;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_74, 0);
x_99 = lean_ctor_get(x_74, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_74);
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
lean_free_object(x_67);
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_71);
if (x_101 == 0)
{
return x_71;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_71, 0);
x_103 = lean_ctor_get(x_71, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_71);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_67, 1);
lean_inc(x_105);
lean_dec(x_67);
lean_inc(x_3);
x_106 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_18);
x_109 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_30, 0);
lean_inc(x_112);
x_113 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_112, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_111);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_117 = l_Lean_MessageData_ofExpr(x_107);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
lean_ctor_set_tag(x_60, 7);
lean_ctor_set(x_60, 1, x_119);
lean_ctor_set(x_60, 0, x_118);
x_120 = l_Lean_MessageData_ofExpr(x_110);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_120);
lean_ctor_set(x_5, 0, x_60);
x_121 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_MessageData_ofExpr(x_114);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_59, x_126, x_12, x_13, x_14, x_15, x_115);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_15;
x_41 = x_128;
goto block_58;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_110);
lean_dec(x_107);
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_131 = x_113;
} else {
 lean_dec_ref(x_113);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_107);
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_133 = lean_ctor_get(x_109, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_109, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_135 = x_109;
} else {
 lean_dec_ref(x_109);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_137 = lean_ctor_get(x_106, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_106, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_139 = x_106;
} else {
 lean_dec_ref(x_106);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
lean_free_object(x_60);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
return x_67;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_60, 1);
lean_inc(x_141);
lean_dec(x_60);
x_142 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
lean_inc(x_3);
x_145 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_18);
x_148 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_30, 0);
lean_inc(x_151);
x_152 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_151, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_150);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_156 = l_Lean_MessageData_ofExpr(x_146);
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(7, 2, 0);
} else {
 x_157 = x_144;
 lean_ctor_set_tag(x_157, 7);
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_MessageData_ofExpr(x_149);
lean_ctor_set_tag(x_5, 7);
lean_ctor_set(x_5, 1, x_160);
lean_ctor_set(x_5, 0, x_159);
x_161 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_5);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_MessageData_ofExpr(x_153);
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_166 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_59, x_166, x_12, x_13, x_14, x_15, x_154);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_32 = x_7;
x_33 = x_8;
x_34 = x_9;
x_35 = x_10;
x_36 = x_11;
x_37 = x_12;
x_38 = x_13;
x_39 = x_14;
x_40 = x_15;
x_41 = x_168;
goto block_58;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_152, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_171 = x_152;
} else {
 lean_dec_ref(x_152);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_148, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_148, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_175 = x_148;
} else {
 lean_dec_ref(x_148);
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
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_144);
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_177 = lean_ctor_get(x_145, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_145, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_179 = x_145;
} else {
 lean_dec_ref(x_145);
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
lean_dec(x_30);
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
return x_142;
}
}
}
block_58:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_30, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_30, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_30, 4);
lean_inc(x_46);
lean_dec(x_30);
lean_inc(x_3);
x_47 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_3);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_18);
x_48 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_42, x_47, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_49, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39, x_40, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_1);
x_53 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_23, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_52);
return x_53;
}
else
{
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
return x_51;
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_48);
if (x_54 == 0)
{
return x_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_48, 0);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_48);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_181; 
lean_free_object(x_5);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_29);
if (x_181 == 0)
{
return x_29;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_29, 0);
x_183 = lean_ctor_get(x_29, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_29);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_185 = lean_ctor_get(x_5, 1);
lean_inc(x_185);
lean_dec(x_5);
x_186 = lean_ctor_get(x_19, 1);
lean_inc(x_186);
x_187 = l_Lean_Grind_CommRing_Mon_sharesVar(x_2, x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_188 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_185, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
x_190 = l_Lean_Grind_CommRing_Poly_spolM(x_189, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_220 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1;
x_221 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_220, x_14, x_192);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_10;
x_197 = x_11;
x_198 = x_12;
x_199 = x_13;
x_200 = x_14;
x_201 = x_15;
x_202 = x_224;
goto block_219;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_226 = x_221;
} else {
 lean_dec_ref(x_221);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Meta_Grind_updateLastTag(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
lean_inc(x_3);
x_230 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_18);
x_233 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_191, 0);
lean_inc(x_236);
x_237 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_236, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_240 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_241 = l_Lean_MessageData_ofExpr(x_231);
if (lean_is_scalar(x_229)) {
 x_242 = lean_alloc_ctor(7, 2, 0);
} else {
 x_242 = x_229;
 lean_ctor_set_tag(x_242, 7);
}
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3;
if (lean_is_scalar(x_226)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_226;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = l_Lean_MessageData_ofExpr(x_234);
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_MessageData_ofExpr(x_238);
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7;
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_220, x_252, x_12, x_13, x_14, x_15, x_239);
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_193 = x_7;
x_194 = x_8;
x_195 = x_9;
x_196 = x_10;
x_197 = x_11;
x_198 = x_12;
x_199 = x_13;
x_200 = x_14;
x_201 = x_15;
x_202 = x_254;
goto block_219;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_234);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_255 = lean_ctor_get(x_237, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_237, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_257 = x_237;
} else {
 lean_dec_ref(x_237);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_259 = lean_ctor_get(x_233, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_233, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_261 = x_233;
} else {
 lean_dec_ref(x_233);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_229);
lean_dec(x_226);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_263 = lean_ctor_get(x_230, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_230, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_265 = x_230;
} else {
 lean_dec_ref(x_230);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_dec(x_226);
lean_dec(x_191);
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
return x_227;
}
}
block_219:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_ctor_get(x_191, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_191, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_191, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_191, 3);
lean_inc(x_206);
x_207 = lean_ctor_get(x_191, 4);
lean_inc(x_207);
lean_dec(x_191);
lean_inc(x_3);
x_208 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_208, 0, x_204);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_3);
lean_ctor_set(x_208, 3, x_206);
lean_ctor_set(x_208, 4, x_207);
lean_ctor_set(x_208, 5, x_18);
x_209 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_203, x_208, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_202);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_210, x_193, x_194, x_195, x_196, x_197, x_198, x_199, x_200, x_201, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
lean_inc(x_1);
x_214 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_185, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_213);
return x_214;
}
else
{
lean_dec(x_185);
lean_dec(x_3);
lean_dec(x_1);
return x_212;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_185);
lean_dec(x_3);
lean_dec(x_1);
x_215 = lean_ctor_get(x_209, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_209, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_217 = x_209;
} else {
 lean_dec_ref(x_209);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_185);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_1);
x_267 = lean_ctor_get(x_190, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_190, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_269 = x_190;
} else {
 lean_dec_ref(x_190);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_3, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_15);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 25);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
lean_inc(x_27);
x_29 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg(x_28, x_23, x_1, x_27, x_27, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_27);
lean_dec(x_23);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
return x_29;
}
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_12, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_12, 0, x_40);
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_dec(x_12);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_27; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_74; lean_object* x_97; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_97 = lean_ctor_get(x_12, 0);
lean_inc(x_97);
x_74 = x_97;
goto block_96;
block_25:
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_18 = lean_int_dec_lt(x_15, x_17);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1;
x_21 = l_Lean_Grind_CommRing_Poly_mulConst(x_20, x_12);
x_22 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
block_32:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Grind_CommRing_Poly_divConst(x_12, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_1);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_13);
lean_ctor_set(x_30, 3, x_14);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
block_39:
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_37 = lean_int_dec_lt(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
x_26 = x_34;
x_27 = x_33;
goto block_32;
}
else
{
lean_object* x_38; 
x_38 = lean_int_neg(x_33);
lean_dec(x_33);
x_26 = x_34;
x_27 = x_38;
goto block_32;
}
}
block_65:
{
lean_object* x_53; 
x_53 = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50, x_51, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_42);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_15 = x_40;
x_16 = x_56;
goto block_25;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = l_Lean_Grind_CommRing_Poly_gcdCoeffs(x_12);
x_59 = lean_nat_to_int(x_58);
x_60 = lean_int_dec_eq(x_59, x_42);
lean_dec(x_42);
if (x_60 == 0)
{
x_33 = x_59;
x_34 = x_57;
x_35 = x_40;
goto block_39;
}
else
{
if (x_41 == 0)
{
lean_dec(x_59);
x_15 = x_40;
x_16 = x_57;
goto block_25;
}
else
{
x_33 = x_59;
x_34 = x_57;
x_35 = x_40;
goto block_39;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
block_73:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = l_Lean_Grind_CommRing_Poly_mulConstC(x_68, x_12, x_67);
x_70 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_1);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_13);
lean_ctor_set(x_71, 3, x_14);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
block_96:
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
x_76 = lean_int_dec_eq(x_74, x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___at___Lean_Grind_CommRing_Expr_toPolyM_spec__0(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_40 = x_74;
x_41 = x_76;
x_42 = x_75;
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
x_47 = x_6;
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_79;
goto block_65;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
lean_inc(x_81);
x_82 = lean_nat_to_int(x_81);
x_83 = l_Lean_Meta_Grind_Arith_gcdExt(x_74, x_82);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 0);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_int_dec_eq(x_85, x_75);
lean_dec(x_85);
if (x_87 == 0)
{
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_81);
x_40 = x_74;
x_41 = x_76;
x_42 = x_75;
x_43 = x_2;
x_44 = x_3;
x_45 = x_4;
x_46 = x_5;
x_47 = x_6;
x_48 = x_7;
x_49 = x_8;
x_50 = x_9;
x_51 = x_10;
x_52 = x_80;
goto block_65;
}
else
{
lean_object* x_88; uint8_t x_89; 
lean_dec(x_74);
x_88 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_89 = lean_int_dec_lt(x_86, x_88);
if (x_89 == 0)
{
lean_dec(x_82);
x_66 = x_80;
x_67 = x_81;
x_68 = x_86;
goto block_73;
}
else
{
lean_object* x_90; 
x_90 = lean_int_emod(x_86, x_82);
lean_dec(x_82);
lean_dec(x_86);
x_66 = x_80;
x_67 = x_81;
x_68 = x_90;
goto block_73;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_74);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_1);
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
else
{
lean_object* x_95; 
lean_dec(x_74);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_11);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpBasis", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simplified: ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = l_List_reverse___redArg(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 0);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_20;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_4);
x_3 = x_23;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_3, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_Grind_CommRing_Mon_divides(x_2, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_27;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_32; 
lean_free_object(x_3);
lean_inc(x_1);
x_32 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively(x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_63 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1;
x_64 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_63, x_12, x_34);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_67;
goto block_62;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
x_70 = lean_ctor_get(x_64, 0);
lean_dec(x_70);
lean_inc(x_33);
x_71 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3;
x_75 = l_Lean_MessageData_ofExpr(x_72);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_75);
lean_ctor_set(x_64, 0, x_74);
x_76 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_63, x_77, x_10, x_11, x_12, x_13, x_73);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_79;
goto block_62;
}
else
{
uint8_t x_80; 
lean_free_object(x_64);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_71);
if (x_80 == 0)
{
return x_71;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_71, 0);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_71);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_dec(x_64);
lean_inc(x_33);
x_85 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3;
x_89 = l_Lean_MessageData_ofExpr(x_86);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_63, x_92, x_10, x_11, x_12, x_13, x_87);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_9;
x_40 = x_10;
x_41 = x_11;
x_42 = x_12;
x_43 = x_13;
x_44 = x_94;
goto block_62;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_95 = lean_ctor_get(x_85, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_97 = x_85;
} else {
 lean_dec_ref(x_85);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
block_62:
{
lean_object* x_45; 
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_33);
x_45 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant(x_33, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_33, x_35, x_36, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_3 = x_27;
x_5 = x_35;
x_6 = x_36;
x_7 = x_37;
x_8 = x_38;
x_9 = x_39;
x_10 = x_40;
x_11 = x_41;
x_12 = x_42;
x_13 = x_43;
x_14 = x_50;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
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
lean_dec(x_33);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
x_3 = x_27;
x_5 = x_35;
x_6 = x_36;
x_7 = x_37;
x_8 = x_38;
x_9 = x_39;
x_10 = x_40;
x_11 = x_41;
x_12 = x_42;
x_13 = x_43;
x_14 = x_56;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_32);
if (x_99 == 0)
{
return x_32;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_32, 0);
x_101 = lean_ctor_get(x_32, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_32);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_3, 1);
lean_inc(x_103);
lean_dec(x_3);
x_104 = lean_ctor_get(x_18, 1);
lean_inc(x_104);
lean_dec(x_18);
x_105 = l_Lean_Grind_CommRing_Mon_divides(x_2, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_17);
lean_ctor_set(x_106, 1, x_4);
x_3 = x_103;
x_4 = x_106;
goto _start;
}
else
{
lean_object* x_108; 
lean_inc(x_1);
x_108 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyWithExhaustively(x_17, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_139 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1;
x_140 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_139, x_12, x_110);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_111 = x_5;
x_112 = x_6;
x_113 = x_7;
x_114 = x_8;
x_115 = x_9;
x_116 = x_10;
x_117 = x_11;
x_118 = x_12;
x_119 = x_13;
x_120 = x_143;
goto block_138;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_145 = x_140;
} else {
 lean_dec_ref(x_140);
 x_145 = lean_box(0);
}
lean_inc(x_109);
x_146 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_109, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_144);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3;
x_150 = l_Lean_MessageData_ofExpr(x_147);
if (lean_is_scalar(x_145)) {
 x_151 = lean_alloc_ctor(7, 2, 0);
} else {
 x_151 = x_145;
 lean_ctor_set_tag(x_151, 7);
}
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_139, x_153, x_10, x_11, x_12, x_13, x_148);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_111 = x_5;
x_112 = x_6;
x_113 = x_7;
x_114 = x_8;
x_115 = x_9;
x_116 = x_10;
x_117 = x_11;
x_118 = x_12;
x_119 = x_13;
x_120 = x_155;
goto block_138;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_145);
lean_dec(x_109);
lean_dec(x_103);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_156 = lean_ctor_get(x_146, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_146, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_158 = x_146;
} else {
 lean_dec_ref(x_146);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
block_138:
{
lean_object* x_121; 
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_109);
x_121 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant(x_109, x_111, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_109, x_111, x_112, x_113, x_114, x_115, x_116, x_117, x_118, x_119, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_3 = x_103;
x_5 = x_111;
x_6 = x_112;
x_7 = x_113;
x_8 = x_114;
x_9 = x_115;
x_10 = x_116;
x_11 = x_117;
x_12 = x_118;
x_13 = x_119;
x_14 = x_126;
goto _start;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_103);
lean_dec(x_4);
lean_dec(x_1);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_130 = x_125;
} else {
 lean_dec_ref(x_125);
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
else
{
lean_object* x_132; 
lean_dec(x_109);
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_dec(x_121);
x_3 = x_103;
x_5 = x_111;
x_6 = x_112;
x_7 = x_113;
x_8 = x_114;
x_9 = x_115;
x_10 = x_116;
x_11 = x_117;
x_12 = x_118;
x_13 = x_119;
x_14 = x_132;
goto _start;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_103);
lean_dec(x_4);
lean_dec(x_1);
x_134 = lean_ctor_get(x_121, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_136 = x_121;
} else {
 lean_dec_ref(x_121);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_103);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_160 = lean_ctor_get(x_108, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_108, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_162 = x_108;
} else {
 lean_dec_ref(x_108);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("using: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_148 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1;
x_149 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_148, x_9, x_11);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_152;
goto block_147;
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_149);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_149, 1);
x_155 = lean_ctor_get(x_149, 0);
lean_dec(x_155);
lean_inc(x_1);
x_156 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1;
x_160 = l_Lean_MessageData_ofExpr(x_157);
lean_ctor_set_tag(x_149, 7);
lean_ctor_set(x_149, 1, x_160);
lean_ctor_set(x_149, 0, x_159);
x_161 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_148, x_162, x_7, x_8, x_9, x_10, x_158);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_164;
goto block_147;
}
else
{
uint8_t x_165; 
lean_free_object(x_149);
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
x_165 = !lean_is_exclusive(x_156);
if (x_165 == 0)
{
return x_156;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_156, 0);
x_167 = lean_ctor_get(x_156, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_156);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_149, 1);
lean_inc(x_169);
lean_dec(x_149);
lean_inc(x_1);
x_170 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1;
x_174 = l_Lean_MessageData_ofExpr(x_171);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_148, x_177, x_7, x_8, x_9, x_10, x_172);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_48 = x_2;
x_49 = x_3;
x_50 = x_4;
x_51 = x_5;
x_52 = x_6;
x_53 = x_7;
x_54 = x_8;
x_55 = x_9;
x_56 = x_10;
x_57 = x_179;
goto block_147;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
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
x_180 = lean_ctor_get(x_170, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_170, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_182 = x_170;
} else {
 lean_dec_ref(x_170);
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
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_23);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_34);
x_39 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_30);
lean_ctor_set(x_39, 2, x_14);
lean_ctor_set(x_39, 3, x_13);
lean_ctor_set(x_39, 4, x_32);
lean_ctor_set(x_39, 5, x_24);
lean_ctor_set(x_39, 6, x_19);
lean_ctor_set(x_39, 7, x_17);
lean_ctor_set(x_39, 8, x_33);
lean_ctor_set(x_39, 9, x_20);
lean_ctor_set(x_39, 10, x_35);
lean_ctor_set(x_39, 11, x_12);
lean_ctor_set(x_39, 12, x_28);
lean_ctor_set(x_39, 13, x_25);
lean_ctor_set(x_39, 14, x_38);
lean_ctor_set(x_39, 15, x_16);
lean_ctor_set_uint8(x_39, sizeof(void*)*16, x_15);
x_40 = lean_st_ref_set(x_29, x_39, x_27);
lean_dec(x_29);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_147:
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_57);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 25);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_box(0);
lean_inc(x_49);
lean_inc(x_48);
x_67 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go(x_1, x_61, x_65, x_66, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55, x_56, x_64);
lean_dec(x_61);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_take(x_49, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 14);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_ctor_get(x_48, 0);
lean_inc(x_75);
lean_dec(x_48);
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_71, 3);
lean_inc(x_79);
x_80 = lean_ctor_get(x_71, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_71, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 7);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_71, sizeof(void*)*16);
x_85 = lean_ctor_get(x_71, 8);
lean_inc(x_85);
x_86 = lean_ctor_get(x_71, 9);
lean_inc(x_86);
x_87 = lean_ctor_get(x_71, 10);
lean_inc(x_87);
x_88 = lean_ctor_get(x_71, 11);
lean_inc(x_88);
x_89 = lean_ctor_get(x_71, 12);
lean_inc(x_89);
x_90 = lean_ctor_get(x_71, 13);
lean_inc(x_90);
x_91 = lean_ctor_get(x_71, 15);
lean_inc(x_91);
lean_dec(x_71);
x_92 = lean_ctor_get(x_72, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_72, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_72, 3);
lean_inc(x_94);
lean_dec(x_72);
x_95 = lean_ctor_get(x_73, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_73, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_73, 2);
lean_inc(x_97);
x_98 = lean_ctor_get(x_73, 3);
lean_inc(x_98);
lean_dec(x_73);
x_99 = lean_array_get_size(x_95);
x_100 = lean_nat_dec_lt(x_75, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_dec(x_75);
lean_dec(x_68);
x_12 = x_88;
x_13 = x_79;
x_14 = x_78;
x_15 = x_84;
x_16 = x_91;
x_17 = x_83;
x_18 = x_76;
x_19 = x_82;
x_20 = x_86;
x_21 = x_96;
x_22 = x_97;
x_23 = x_98;
x_24 = x_81;
x_25 = x_90;
x_26 = x_93;
x_27 = x_74;
x_28 = x_89;
x_29 = x_49;
x_30 = x_77;
x_31 = x_92;
x_32 = x_80;
x_33 = x_85;
x_34 = x_94;
x_35 = x_87;
x_36 = x_95;
goto block_47;
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_array_fget(x_95, x_75);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_101, 25);
lean_dec(x_103);
x_104 = lean_box(0);
x_105 = lean_array_fset(x_95, x_75, x_104);
lean_ctor_set(x_101, 25, x_68);
x_106 = lean_array_fset(x_105, x_75, x_101);
lean_dec(x_75);
x_12 = x_88;
x_13 = x_79;
x_14 = x_78;
x_15 = x_84;
x_16 = x_91;
x_17 = x_83;
x_18 = x_76;
x_19 = x_82;
x_20 = x_86;
x_21 = x_96;
x_22 = x_97;
x_23 = x_98;
x_24 = x_81;
x_25 = x_90;
x_26 = x_93;
x_27 = x_74;
x_28 = x_89;
x_29 = x_49;
x_30 = x_77;
x_31 = x_92;
x_32 = x_80;
x_33 = x_85;
x_34 = x_94;
x_35 = x_87;
x_36 = x_106;
goto block_47;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_107 = lean_ctor_get(x_101, 0);
x_108 = lean_ctor_get(x_101, 1);
x_109 = lean_ctor_get(x_101, 2);
x_110 = lean_ctor_get(x_101, 3);
x_111 = lean_ctor_get(x_101, 4);
x_112 = lean_ctor_get(x_101, 5);
x_113 = lean_ctor_get(x_101, 6);
x_114 = lean_ctor_get(x_101, 7);
x_115 = lean_ctor_get(x_101, 8);
x_116 = lean_ctor_get(x_101, 9);
x_117 = lean_ctor_get(x_101, 10);
x_118 = lean_ctor_get(x_101, 11);
x_119 = lean_ctor_get(x_101, 12);
x_120 = lean_ctor_get(x_101, 13);
x_121 = lean_ctor_get(x_101, 14);
x_122 = lean_ctor_get(x_101, 15);
x_123 = lean_ctor_get(x_101, 16);
x_124 = lean_ctor_get(x_101, 17);
x_125 = lean_ctor_get(x_101, 18);
x_126 = lean_ctor_get(x_101, 19);
x_127 = lean_ctor_get(x_101, 20);
x_128 = lean_ctor_get(x_101, 21);
x_129 = lean_ctor_get(x_101, 22);
x_130 = lean_ctor_get(x_101, 23);
x_131 = lean_ctor_get(x_101, 24);
x_132 = lean_ctor_get(x_101, 26);
x_133 = lean_ctor_get_uint8(x_101, sizeof(void*)*28);
x_134 = lean_ctor_get(x_101, 27);
lean_inc(x_134);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_101);
x_135 = lean_box(0);
x_136 = lean_array_fset(x_95, x_75, x_135);
x_137 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_137, 0, x_107);
lean_ctor_set(x_137, 1, x_108);
lean_ctor_set(x_137, 2, x_109);
lean_ctor_set(x_137, 3, x_110);
lean_ctor_set(x_137, 4, x_111);
lean_ctor_set(x_137, 5, x_112);
lean_ctor_set(x_137, 6, x_113);
lean_ctor_set(x_137, 7, x_114);
lean_ctor_set(x_137, 8, x_115);
lean_ctor_set(x_137, 9, x_116);
lean_ctor_set(x_137, 10, x_117);
lean_ctor_set(x_137, 11, x_118);
lean_ctor_set(x_137, 12, x_119);
lean_ctor_set(x_137, 13, x_120);
lean_ctor_set(x_137, 14, x_121);
lean_ctor_set(x_137, 15, x_122);
lean_ctor_set(x_137, 16, x_123);
lean_ctor_set(x_137, 17, x_124);
lean_ctor_set(x_137, 18, x_125);
lean_ctor_set(x_137, 19, x_126);
lean_ctor_set(x_137, 20, x_127);
lean_ctor_set(x_137, 21, x_128);
lean_ctor_set(x_137, 22, x_129);
lean_ctor_set(x_137, 23, x_130);
lean_ctor_set(x_137, 24, x_131);
lean_ctor_set(x_137, 25, x_68);
lean_ctor_set(x_137, 26, x_132);
lean_ctor_set(x_137, 27, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*28, x_133);
x_138 = lean_array_fset(x_136, x_75, x_137);
lean_dec(x_75);
x_12 = x_88;
x_13 = x_79;
x_14 = x_78;
x_15 = x_84;
x_16 = x_91;
x_17 = x_83;
x_18 = x_76;
x_19 = x_82;
x_20 = x_86;
x_21 = x_96;
x_22 = x_97;
x_23 = x_98;
x_24 = x_81;
x_25 = x_90;
x_26 = x_93;
x_27 = x_74;
x_28 = x_89;
x_29 = x_49;
x_30 = x_77;
x_31 = x_92;
x_32 = x_80;
x_33 = x_85;
x_34 = x_94;
x_35 = x_87;
x_36 = x_138;
goto block_47;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_49);
lean_dec(x_48);
x_139 = !lean_is_exclusive(x_67);
if (x_139 == 0)
{
return x_67;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_67, 0);
x_141 = lean_ctor_get(x_67, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_67);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_61);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_62);
if (x_143 == 0)
{
return x_62;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_62, 0);
x_145 = lean_ctor_get(x_62, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_62);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_13);
x_17 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0;
x_20 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_19, x_9, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 1);
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
lean_inc(x_13);
x_32 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_36 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_35);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_35);
lean_ctor_set(x_20, 0, x_28);
x_37 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_19, x_20, x_7, x_8, x_9, x_10, x_34);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
else
{
uint8_t x_40; 
lean_free_object(x_28);
lean_free_object(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec(x_28);
lean_inc(x_13);
x_45 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_49 = l_Lean_MessageData_ofExpr(x_46);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_48);
lean_ctor_set(x_20, 0, x_50);
x_51 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_19, x_20, x_7, x_8, x_9, x_10, x_47);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
lean_free_object(x_20);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_28;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_dec(x_20);
x_59 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
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
lean_inc(x_13);
x_62 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_66 = l_Lean_MessageData_ofExpr(x_63);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(7, 2, 0);
} else {
 x_67 = x_61;
 lean_ctor_set_tag(x_67, 7);
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
x_69 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_19, x_68, x_7, x_8, x_9, x_10, x_64);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_61);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_74 = x_62;
} else {
 lean_dec_ref(x_62);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_59;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
else
{
uint8_t x_76; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_12);
if (x_76 == 0)
{
return x_12;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_12, 0);
x_78 = lean_ctor_get(x_12, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_12);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyAndCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyAndCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = l_Lean_Grind_CommRing_Poly_degree(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_checkConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_1, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec(x_75);
x_16 = x_76;
goto block_74;
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_74:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_19 = lean_int_dec_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5;
x_21 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_20, x_9, x_11);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
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
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_12 = x_24;
goto block_15;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_34 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_34);
lean_ctor_set(x_21, 0, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_20, x_35, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_12 = x_37;
goto block_15;
}
else
{
uint8_t x_38; 
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
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
lean_free_object(x_21);
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
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_dec(x_21);
x_47 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_53 = l_Lean_MessageData_ofExpr(x_50);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
x_56 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_20, x_55, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_12 = x_57;
goto block_15;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_60 = x_49;
} else {
 lean_dec_ref(x_49);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_64 = x_47;
} else {
 lean_dec_ref(x_47);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
else
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_12 = x_67;
goto block_15;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_66);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_16);
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
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_11);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_1, 4);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
lean_ctor_set_uint8(x_2, sizeof(void*)*1, x_20);
x_21 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_1, 4, x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_1, 4, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_1);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
x_35 = lean_ctor_get(x_1, 4);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(1);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_35, x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
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
lean_ctor_set(x_1, 4, x_41);
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_1);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_ctor_get(x_1, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_55 = x_2;
} else {
 lean_dec_ref(x_2);
 x_55 = lean_box(0);
}
x_56 = lean_box(1);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 1, 1);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_54);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_53, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_63, 2, x_51);
lean_ctor_set(x_63, 3, x_52);
lean_ctor_set(x_63, 4, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1;
x_125 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_124, x_9, x_11);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_48 = x_2;
x_49 = x_3;
x_50 = x_128;
goto block_123;
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 1);
x_131 = lean_ctor_get(x_125, 0);
lean_dec(x_131);
x_132 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 1);
x_135 = lean_ctor_get(x_132, 0);
lean_dec(x_135);
lean_inc(x_1);
x_136 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_140 = l_Lean_MessageData_ofExpr(x_137);
lean_ctor_set_tag(x_132, 7);
lean_ctor_set(x_132, 1, x_140);
lean_ctor_set(x_132, 0, x_139);
lean_ctor_set_tag(x_125, 7);
lean_ctor_set(x_125, 1, x_139);
lean_ctor_set(x_125, 0, x_132);
x_141 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_124, x_125, x_7, x_8, x_9, x_10, x_138);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_48 = x_2;
x_49 = x_3;
x_50 = x_142;
goto block_123;
}
else
{
uint8_t x_143; 
lean_free_object(x_132);
lean_free_object(x_125);
lean_dec(x_1);
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
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_132, 1);
lean_inc(x_147);
lean_dec(x_132);
lean_inc(x_1);
x_148 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_152 = l_Lean_MessageData_ofExpr(x_149);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_tag(x_125, 7);
lean_ctor_set(x_125, 1, x_151);
lean_ctor_set(x_125, 0, x_153);
x_154 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_124, x_125, x_7, x_8, x_9, x_10, x_150);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_48 = x_2;
x_49 = x_3;
x_50 = x_155;
goto block_123;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_free_object(x_125);
lean_dec(x_1);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_158 = x_148;
} else {
 lean_dec_ref(x_148);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
else
{
lean_free_object(x_125);
lean_dec(x_1);
return x_132;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_125, 1);
lean_inc(x_160);
lean_dec(x_125);
x_161 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
lean_inc(x_1);
x_164 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setDiseqUnsat_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_168 = l_Lean_MessageData_ofExpr(x_165);
if (lean_is_scalar(x_163)) {
 x_169 = lean_alloc_ctor(7, 2, 0);
} else {
 x_169 = x_163;
 lean_ctor_set_tag(x_169, 7);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
x_171 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_124, x_170, x_7, x_8, x_9, x_10, x_166);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_48 = x_2;
x_49 = x_3;
x_50 = x_172;
goto block_123;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_163);
lean_dec(x_1);
x_173 = lean_ctor_get(x_164, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
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
else
{
lean_dec(x_1);
return x_161;
}
}
}
block_47:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_33);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_16);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_28);
x_39 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_24);
lean_ctor_set(x_39, 3, x_22);
lean_ctor_set(x_39, 4, x_14);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_15);
lean_ctor_set(x_39, 7, x_20);
lean_ctor_set(x_39, 8, x_30);
lean_ctor_set(x_39, 9, x_13);
lean_ctor_set(x_39, 10, x_21);
lean_ctor_set(x_39, 11, x_18);
lean_ctor_set(x_39, 12, x_12);
lean_ctor_set(x_39, 13, x_27);
lean_ctor_set(x_39, 14, x_38);
lean_ctor_set(x_39, 15, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*16, x_19);
x_40 = lean_st_ref_set(x_23, x_39, x_17);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
block_123:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_51 = lean_st_ref_take(x_49, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 14);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_52, 7);
lean_inc(x_64);
x_65 = lean_ctor_get_uint8(x_52, sizeof(void*)*16);
x_66 = lean_ctor_get(x_52, 8);
lean_inc(x_66);
x_67 = lean_ctor_get(x_52, 9);
lean_inc(x_67);
x_68 = lean_ctor_get(x_52, 10);
lean_inc(x_68);
x_69 = lean_ctor_get(x_52, 11);
lean_inc(x_69);
x_70 = lean_ctor_get(x_52, 12);
lean_inc(x_70);
x_71 = lean_ctor_get(x_52, 13);
lean_inc(x_71);
x_72 = lean_ctor_get(x_52, 15);
lean_inc(x_72);
lean_dec(x_52);
x_73 = lean_ctor_get(x_53, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_53, 3);
lean_inc(x_75);
lean_dec(x_53);
x_76 = lean_ctor_get(x_54, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_54, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_54, 3);
lean_inc(x_79);
lean_dec(x_54);
x_80 = lean_array_get_size(x_76);
x_81 = lean_nat_dec_lt(x_56, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_dec(x_1);
x_12 = x_70;
x_13 = x_67;
x_14 = x_61;
x_15 = x_63;
x_16 = x_74;
x_17 = x_55;
x_18 = x_69;
x_19 = x_65;
x_20 = x_64;
x_21 = x_68;
x_22 = x_60;
x_23 = x_49;
x_24 = x_59;
x_25 = x_73;
x_26 = x_57;
x_27 = x_71;
x_28 = x_75;
x_29 = x_58;
x_30 = x_66;
x_31 = x_77;
x_32 = x_78;
x_33 = x_79;
x_34 = x_72;
x_35 = x_62;
x_36 = x_76;
goto block_47;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_array_fget(x_76, x_56);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_82, 26);
x_85 = lean_box(0);
x_86 = lean_array_fset(x_76, x_56, x_85);
x_87 = l_Lean_PersistentArray_push___redArg(x_84, x_1);
lean_ctor_set(x_82, 26, x_87);
x_88 = lean_array_fset(x_86, x_56, x_82);
x_12 = x_70;
x_13 = x_67;
x_14 = x_61;
x_15 = x_63;
x_16 = x_74;
x_17 = x_55;
x_18 = x_69;
x_19 = x_65;
x_20 = x_64;
x_21 = x_68;
x_22 = x_60;
x_23 = x_49;
x_24 = x_59;
x_25 = x_73;
x_26 = x_57;
x_27 = x_71;
x_28 = x_75;
x_29 = x_58;
x_30 = x_66;
x_31 = x_77;
x_32 = x_78;
x_33 = x_79;
x_34 = x_72;
x_35 = x_62;
x_36 = x_88;
goto block_47;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
x_91 = lean_ctor_get(x_82, 2);
x_92 = lean_ctor_get(x_82, 3);
x_93 = lean_ctor_get(x_82, 4);
x_94 = lean_ctor_get(x_82, 5);
x_95 = lean_ctor_get(x_82, 6);
x_96 = lean_ctor_get(x_82, 7);
x_97 = lean_ctor_get(x_82, 8);
x_98 = lean_ctor_get(x_82, 9);
x_99 = lean_ctor_get(x_82, 10);
x_100 = lean_ctor_get(x_82, 11);
x_101 = lean_ctor_get(x_82, 12);
x_102 = lean_ctor_get(x_82, 13);
x_103 = lean_ctor_get(x_82, 14);
x_104 = lean_ctor_get(x_82, 15);
x_105 = lean_ctor_get(x_82, 16);
x_106 = lean_ctor_get(x_82, 17);
x_107 = lean_ctor_get(x_82, 18);
x_108 = lean_ctor_get(x_82, 19);
x_109 = lean_ctor_get(x_82, 20);
x_110 = lean_ctor_get(x_82, 21);
x_111 = lean_ctor_get(x_82, 22);
x_112 = lean_ctor_get(x_82, 23);
x_113 = lean_ctor_get(x_82, 24);
x_114 = lean_ctor_get(x_82, 25);
x_115 = lean_ctor_get(x_82, 26);
x_116 = lean_ctor_get_uint8(x_82, sizeof(void*)*28);
x_117 = lean_ctor_get(x_82, 27);
lean_inc(x_117);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_118 = lean_box(0);
x_119 = lean_array_fset(x_76, x_56, x_118);
x_120 = l_Lean_PersistentArray_push___redArg(x_115, x_1);
x_121 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_121, 0, x_89);
lean_ctor_set(x_121, 1, x_90);
lean_ctor_set(x_121, 2, x_91);
lean_ctor_set(x_121, 3, x_92);
lean_ctor_set(x_121, 4, x_93);
lean_ctor_set(x_121, 5, x_94);
lean_ctor_set(x_121, 6, x_95);
lean_ctor_set(x_121, 7, x_96);
lean_ctor_set(x_121, 8, x_97);
lean_ctor_set(x_121, 9, x_98);
lean_ctor_set(x_121, 10, x_99);
lean_ctor_set(x_121, 11, x_100);
lean_ctor_set(x_121, 12, x_101);
lean_ctor_set(x_121, 13, x_102);
lean_ctor_set(x_121, 14, x_103);
lean_ctor_set(x_121, 15, x_104);
lean_ctor_set(x_121, 16, x_105);
lean_ctor_set(x_121, 17, x_106);
lean_ctor_set(x_121, 18, x_107);
lean_ctor_set(x_121, 19, x_108);
lean_ctor_set(x_121, 20, x_109);
lean_ctor_set(x_121, 21, x_110);
lean_ctor_set(x_121, 22, x_111);
lean_ctor_set(x_121, 23, x_112);
lean_ctor_set(x_121, 24, x_113);
lean_ctor_set(x_121, 25, x_114);
lean_ctor_set(x_121, 26, x_120);
lean_ctor_set(x_121, 27, x_117);
lean_ctor_set_uint8(x_121, sizeof(void*)*28, x_116);
x_122 = lean_array_fset(x_119, x_56, x_121);
x_12 = x_70;
x_13 = x_67;
x_14 = x_61;
x_15 = x_63;
x_16 = x_74;
x_17 = x_55;
x_18 = x_69;
x_19 = x_65;
x_20 = x_64;
x_21 = x_68;
x_22 = x_60;
x_23 = x_49;
x_24 = x_59;
x_25 = x_73;
x_26 = x_57;
x_27 = x_71;
x_28 = x_75;
x_29 = x_58;
x_30 = x_66;
x_31 = x_77;
x_32 = x_78;
x_33 = x_79;
x_34 = x_72;
x_35 = x_62;
x_36 = x_122;
goto block_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_saveDiseq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_addNewDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
x_12 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_simplify(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_DiseqCnstr_checkConstant(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_Grind_Arith_CommRing_saveDiseq(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_process_ring_eq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_68; 
x_68 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_1, x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_inc(x_2);
lean_inc(x_1);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(x_1, x_2, x_3, x_11);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
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
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_box(0);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_79 = l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0;
x_80 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_79, x_9, x_77);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_80, 1);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_68);
x_85 = lean_unbox(x_82);
lean_dec(x_82);
if (x_85 == 0)
{
lean_free_object(x_80);
x_12 = x_84;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_83;
goto block_67;
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_83);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_86, 1);
x_89 = lean_ctor_get(x_86, 0);
lean_dec(x_89);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_94 = l_Lean_MessageData_ofExpr(x_91);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_94);
lean_ctor_set(x_86, 0, x_93);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_93);
lean_ctor_set(x_80, 0, x_86);
x_95 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_79, x_80, x_7, x_8, x_9, x_10, x_92);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_12 = x_84;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_96;
goto block_67;
}
else
{
uint8_t x_97; 
lean_free_object(x_86);
lean_dec(x_84);
lean_free_object(x_80);
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
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_86, 1);
lean_inc(x_101);
lean_dec(x_86);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_102 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_106 = l_Lean_MessageData_ofExpr(x_103);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_tag(x_80, 7);
lean_ctor_set(x_80, 1, x_105);
lean_ctor_set(x_80, 0, x_107);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_79, x_80, x_7, x_8, x_9, x_10, x_104);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_12 = x_84;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_109;
goto block_67;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_84);
lean_free_object(x_80);
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
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_112 = x_102;
} else {
 lean_dec_ref(x_102);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
else
{
lean_dec(x_84);
lean_free_object(x_80);
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
return x_86;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_80, 0);
x_115 = lean_ctor_get(x_80, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_80);
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_78);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_68);
x_117 = lean_unbox(x_114);
lean_dec(x_114);
if (x_117 == 0)
{
x_12 = x_116;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_115;
goto block_67;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_121 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_125 = l_Lean_MessageData_ofExpr(x_122);
if (lean_is_scalar(x_120)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_120;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
x_128 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_79, x_127, x_7, x_8, x_9, x_10, x_123);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_12 = x_116;
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = x_9;
x_20 = x_10;
x_21 = x_129;
goto block_67;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_120);
lean_dec(x_116);
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
x_130 = lean_ctor_get(x_121, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_121, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_132 = x_121;
} else {
 lean_dec_ref(x_121);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_dec(x_116);
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
return x_118;
}
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
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
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_11);
return x_135;
}
block_67:
{
lean_object* x_22; 
lean_inc(x_1);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_1, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
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
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_2);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
lean_inc(x_41);
lean_inc(x_31);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_31);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Grind_CommRing_Expr_toPolyM(x_42, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_2);
lean_ctor_set(x_46, 2, x_31);
lean_ctor_set(x_46, 3, x_41);
x_47 = l_Lean_Meta_Grind_Arith_CommRing_mkEqCnstr(x_44, x_46, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_Arith_CommRing_addNewEq(x_48, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_49);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
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
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_43);
if (x_55 == 0)
{
return x_43;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_43, 0);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_43);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
return x_32;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_32, 0);
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_32);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_22);
if (x_63 == 0)
{
return x_22;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_22, 0);
x_65 = lean_ctor_get(x_22, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_22);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_5);
x_11 = l_Lean_Meta_Grind_canon(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_shareCommon___redArg(x_12, x_5, x_13);
lean_dec(x_5);
return x_14;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CommRing", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diseq_to_eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rabinowitsch", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(21u);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr.0.Lean.Meta.Grind.Arith.CommRing.diseqToEq", 97, 97);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(295u);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_260; 
lean_inc(x_1);
x_155 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4, x_12);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_2);
x_158 = l_Lean_Meta_Grind_getGeneration___redArg(x_2, x_4, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_260 = lean_nat_dec_le(x_156, x_159);
if (x_260 == 0)
{
lean_dec(x_159);
x_161 = x_156;
goto block_259;
}
else
{
lean_dec(x_156);
x_161 = x_159;
goto block_259;
}
block_42:
{
lean_object* x_27; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Lean_Meta_Grind_mkDiseqProof(x_1, x_2, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4;
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Expr_const___override(x_30, x_32);
x_34 = l_Lean_mkApp5(x_33, x_17, x_16, x_1, x_2, x_28);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Meta_Grind_pushEqCore(x_14, x_13, x_34, x_36, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_29);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_105:
{
lean_object* x_52; lean_object* x_53; 
lean_inc(x_43);
x_52 = l_Lean_Expr_app___override(x_51, x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(x_52, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_mkAppB(x_46, x_43, x_54);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_58);
x_61 = lean_grind_internalize(x_58, x_45, x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_59);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6;
x_66 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_65, x_10, x_63);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
lean_free_object(x_61);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_13 = x_44;
x_14 = x_58;
x_15 = x_47;
x_16 = x_49;
x_17 = x_50;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_69;
goto block_42;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_66, 1);
x_72 = lean_ctor_get(x_66, 0);
lean_dec(x_72);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_58);
x_74 = l_Lean_MessageData_ofExpr(x_58);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_74);
lean_ctor_set(x_66, 0, x_73);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_66);
x_75 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_65, x_61, x_8, x_9, x_10, x_11, x_71);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_13 = x_44;
x_14 = x_58;
x_15 = x_47;
x_16 = x_49;
x_17 = x_50;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_76;
goto block_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_66, 1);
lean_inc(x_77);
lean_dec(x_66);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_58);
x_79 = l_Lean_MessageData_ofExpr(x_58);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_78);
lean_ctor_set(x_61, 0, x_80);
x_81 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_65, x_61, x_8, x_9, x_10, x_11, x_77);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_13 = x_44;
x_14 = x_58;
x_15 = x_47;
x_16 = x_49;
x_17 = x_50;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_82;
goto block_42;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_61, 1);
lean_inc(x_83);
lean_dec(x_61);
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6;
x_85 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_84, x_10, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_13 = x_44;
x_14 = x_58;
x_15 = x_47;
x_16 = x_49;
x_17 = x_50;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_88;
goto block_42;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_58);
x_92 = l_Lean_MessageData_ofExpr(x_58);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(7, 2, 0);
} else {
 x_93 = x_90;
 lean_ctor_set_tag(x_93, 7);
}
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
x_95 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_84, x_94, x_8, x_9, x_10, x_11, x_89);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_13 = x_44;
x_14 = x_58;
x_15 = x_47;
x_16 = x_49;
x_17 = x_50;
x_18 = x_4;
x_19 = x_5;
x_20 = x_6;
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_11;
x_26 = x_96;
goto block_42;
}
}
}
else
{
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
}
else
{
uint8_t x_97; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_57);
if (x_97 == 0)
{
return x_57;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_57, 0);
x_99 = lean_ctor_get(x_57, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_57);
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
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_53);
if (x_101 == 0)
{
return x_53;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_53, 0);
x_103 = lean_ctor_get(x_53, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_53);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
block_154:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_126);
lean_ctor_set(x_137, 2, x_127);
lean_ctor_set(x_137, 3, x_128);
x_138 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_138, 0, x_115);
lean_ctor_set(x_138, 1, x_123);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_125);
x_139 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_139, 0, x_111);
lean_ctor_set(x_139, 1, x_131);
lean_ctor_set(x_139, 2, x_121);
lean_ctor_set(x_139, 3, x_130);
lean_ctor_set(x_139, 4, x_108);
lean_ctor_set(x_139, 5, x_133);
lean_ctor_set(x_139, 6, x_114);
lean_ctor_set(x_139, 7, x_106);
lean_ctor_set(x_139, 8, x_117);
lean_ctor_set(x_139, 9, x_132);
lean_ctor_set(x_139, 10, x_118);
lean_ctor_set(x_139, 11, x_107);
lean_ctor_set(x_139, 12, x_113);
lean_ctor_set(x_139, 13, x_124);
lean_ctor_set(x_139, 14, x_138);
lean_ctor_set(x_139, 15, x_109);
lean_ctor_set_uint8(x_139, sizeof(void*)*16, x_135);
x_140 = lean_st_ref_set(x_4, x_139, x_129);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_141);
lean_dec(x_3);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_143, 17);
lean_inc(x_144);
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10;
x_147 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_146);
x_43 = x_116;
x_44 = x_112;
x_45 = x_119;
x_46 = x_120;
x_47 = x_110;
x_48 = x_145;
x_49 = x_122;
x_50 = x_134;
x_51 = x_147;
goto block_105;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
lean_dec(x_144);
x_43 = x_116;
x_44 = x_112;
x_45 = x_119;
x_46 = x_120;
x_47 = x_110;
x_48 = x_148;
x_49 = x_122;
x_50 = x_134;
x_51 = x_149;
goto block_105;
}
}
else
{
uint8_t x_150; 
lean_dec(x_134);
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
return x_142;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_142, 0);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_142);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
block_259:
{
lean_object* x_162; 
x_162 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 9);
lean_inc(x_164);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14;
x_167 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_166, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_162, 1);
lean_inc(x_168);
lean_dec(x_162);
x_169 = lean_ctor_get(x_163, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 11);
lean_inc(x_171);
x_172 = lean_ctor_get(x_163, 12);
lean_inc(x_172);
x_173 = lean_ctor_get(x_163, 18);
lean_inc(x_173);
lean_dec(x_163);
x_174 = lean_ctor_get(x_164, 0);
lean_inc(x_174);
lean_dec(x_164);
lean_inc(x_2);
lean_inc(x_1);
x_175 = l_Lean_mkAppB(x_172, x_1, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_176 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(x_175, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_168);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_st_ref_take(x_4, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 14);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_179, 1);
lean_inc(x_183);
lean_dec(x_179);
x_184 = lean_ctor_get(x_3, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_180, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 3);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 4);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 5);
lean_inc(x_190);
x_191 = lean_ctor_get(x_180, 6);
lean_inc(x_191);
x_192 = lean_ctor_get(x_180, 7);
lean_inc(x_192);
x_193 = lean_ctor_get_uint8(x_180, sizeof(void*)*16);
x_194 = lean_ctor_get(x_180, 8);
lean_inc(x_194);
x_195 = lean_ctor_get(x_180, 9);
lean_inc(x_195);
x_196 = lean_ctor_get(x_180, 10);
lean_inc(x_196);
x_197 = lean_ctor_get(x_180, 11);
lean_inc(x_197);
x_198 = lean_ctor_get(x_180, 12);
lean_inc(x_198);
x_199 = lean_ctor_get(x_180, 13);
lean_inc(x_199);
x_200 = lean_ctor_get(x_180, 15);
lean_inc(x_200);
lean_dec(x_180);
x_201 = lean_ctor_get(x_181, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_181, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_181, 3);
lean_inc(x_203);
lean_dec(x_181);
x_204 = lean_ctor_get(x_182, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_182, 1);
lean_inc(x_205);
x_206 = lean_ctor_get(x_182, 2);
lean_inc(x_206);
x_207 = lean_ctor_get(x_182, 3);
lean_inc(x_207);
lean_dec(x_182);
x_208 = lean_array_get_size(x_204);
x_209 = lean_nat_dec_lt(x_184, x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_dec(x_184);
x_106 = x_192;
x_107 = x_197;
x_108 = x_189;
x_109 = x_200;
x_110 = x_170;
x_111 = x_185;
x_112 = x_173;
x_113 = x_198;
x_114 = x_191;
x_115 = x_201;
x_116 = x_177;
x_117 = x_194;
x_118 = x_196;
x_119 = x_161;
x_120 = x_171;
x_121 = x_187;
x_122 = x_174;
x_123 = x_202;
x_124 = x_199;
x_125 = x_203;
x_126 = x_205;
x_127 = x_206;
x_128 = x_207;
x_129 = x_183;
x_130 = x_188;
x_131 = x_186;
x_132 = x_195;
x_133 = x_190;
x_134 = x_169;
x_135 = x_193;
x_136 = x_204;
goto block_154;
}
else
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_array_fget(x_204, x_184);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_210, 27);
x_213 = lean_box(0);
x_214 = lean_array_fset(x_204, x_184, x_213);
lean_inc(x_177);
x_215 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_212, x_177, x_213);
lean_ctor_set(x_210, 27, x_215);
x_216 = lean_array_fset(x_214, x_184, x_210);
lean_dec(x_184);
x_106 = x_192;
x_107 = x_197;
x_108 = x_189;
x_109 = x_200;
x_110 = x_170;
x_111 = x_185;
x_112 = x_173;
x_113 = x_198;
x_114 = x_191;
x_115 = x_201;
x_116 = x_177;
x_117 = x_194;
x_118 = x_196;
x_119 = x_161;
x_120 = x_171;
x_121 = x_187;
x_122 = x_174;
x_123 = x_202;
x_124 = x_199;
x_125 = x_203;
x_126 = x_205;
x_127 = x_206;
x_128 = x_207;
x_129 = x_183;
x_130 = x_188;
x_131 = x_186;
x_132 = x_195;
x_133 = x_190;
x_134 = x_169;
x_135 = x_193;
x_136 = x_216;
goto block_154;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_217 = lean_ctor_get(x_210, 0);
x_218 = lean_ctor_get(x_210, 1);
x_219 = lean_ctor_get(x_210, 2);
x_220 = lean_ctor_get(x_210, 3);
x_221 = lean_ctor_get(x_210, 4);
x_222 = lean_ctor_get(x_210, 5);
x_223 = lean_ctor_get(x_210, 6);
x_224 = lean_ctor_get(x_210, 7);
x_225 = lean_ctor_get(x_210, 8);
x_226 = lean_ctor_get(x_210, 9);
x_227 = lean_ctor_get(x_210, 10);
x_228 = lean_ctor_get(x_210, 11);
x_229 = lean_ctor_get(x_210, 12);
x_230 = lean_ctor_get(x_210, 13);
x_231 = lean_ctor_get(x_210, 14);
x_232 = lean_ctor_get(x_210, 15);
x_233 = lean_ctor_get(x_210, 16);
x_234 = lean_ctor_get(x_210, 17);
x_235 = lean_ctor_get(x_210, 18);
x_236 = lean_ctor_get(x_210, 19);
x_237 = lean_ctor_get(x_210, 20);
x_238 = lean_ctor_get(x_210, 21);
x_239 = lean_ctor_get(x_210, 22);
x_240 = lean_ctor_get(x_210, 23);
x_241 = lean_ctor_get(x_210, 24);
x_242 = lean_ctor_get(x_210, 25);
x_243 = lean_ctor_get(x_210, 26);
x_244 = lean_ctor_get_uint8(x_210, sizeof(void*)*28);
x_245 = lean_ctor_get(x_210, 27);
lean_inc(x_245);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_210);
x_246 = lean_box(0);
x_247 = lean_array_fset(x_204, x_184, x_246);
lean_inc(x_177);
x_248 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_245, x_177, x_246);
x_249 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_249, 0, x_217);
lean_ctor_set(x_249, 1, x_218);
lean_ctor_set(x_249, 2, x_219);
lean_ctor_set(x_249, 3, x_220);
lean_ctor_set(x_249, 4, x_221);
lean_ctor_set(x_249, 5, x_222);
lean_ctor_set(x_249, 6, x_223);
lean_ctor_set(x_249, 7, x_224);
lean_ctor_set(x_249, 8, x_225);
lean_ctor_set(x_249, 9, x_226);
lean_ctor_set(x_249, 10, x_227);
lean_ctor_set(x_249, 11, x_228);
lean_ctor_set(x_249, 12, x_229);
lean_ctor_set(x_249, 13, x_230);
lean_ctor_set(x_249, 14, x_231);
lean_ctor_set(x_249, 15, x_232);
lean_ctor_set(x_249, 16, x_233);
lean_ctor_set(x_249, 17, x_234);
lean_ctor_set(x_249, 18, x_235);
lean_ctor_set(x_249, 19, x_236);
lean_ctor_set(x_249, 20, x_237);
lean_ctor_set(x_249, 21, x_238);
lean_ctor_set(x_249, 22, x_239);
lean_ctor_set(x_249, 23, x_240);
lean_ctor_set(x_249, 24, x_241);
lean_ctor_set(x_249, 25, x_242);
lean_ctor_set(x_249, 26, x_243);
lean_ctor_set(x_249, 27, x_248);
lean_ctor_set_uint8(x_249, sizeof(void*)*28, x_244);
x_250 = lean_array_fset(x_247, x_184, x_249);
lean_dec(x_184);
x_106 = x_192;
x_107 = x_197;
x_108 = x_189;
x_109 = x_200;
x_110 = x_170;
x_111 = x_185;
x_112 = x_173;
x_113 = x_198;
x_114 = x_191;
x_115 = x_201;
x_116 = x_177;
x_117 = x_194;
x_118 = x_196;
x_119 = x_161;
x_120 = x_171;
x_121 = x_187;
x_122 = x_174;
x_123 = x_202;
x_124 = x_199;
x_125 = x_203;
x_126 = x_205;
x_127 = x_206;
x_128 = x_207;
x_129 = x_183;
x_130 = x_188;
x_131 = x_186;
x_132 = x_195;
x_133 = x_190;
x_134 = x_169;
x_135 = x_193;
x_136 = x_250;
goto block_154;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_161);
lean_dec(x_11);
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
x_251 = !lean_is_exclusive(x_176);
if (x_251 == 0)
{
return x_176;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_176, 0);
x_253 = lean_ctor_get(x_176, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_176);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_161);
lean_dec(x_11);
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
x_255 = !lean_is_exclusive(x_162);
if (x_255 == 0)
{
return x_162;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_162, 0);
x_257 = lean_ctor_get(x_162, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_162);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr.0.Lean.Meta.Grind.Arith.CommRing.diseqZeroToEq", 101, 101);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13;
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(308u);
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("diseq0_to_eq", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2;
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 9);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1;
x_22 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_162; uint8_t x_163; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 11);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 18);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_111 = lean_st_ref_take(x_4, x_23);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 14);
lean_inc(x_113);
x_114 = lean_ctor_get(x_113, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_ctor_get(x_3, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_112, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_112, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_112, 4);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 5);
lean_inc(x_122);
x_123 = lean_ctor_get(x_112, 6);
lean_inc(x_123);
x_124 = lean_ctor_get(x_112, 7);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_112, sizeof(void*)*16);
x_126 = lean_ctor_get(x_112, 8);
lean_inc(x_126);
x_127 = lean_ctor_get(x_112, 9);
lean_inc(x_127);
x_128 = lean_ctor_get(x_112, 10);
lean_inc(x_128);
x_129 = lean_ctor_get(x_112, 11);
lean_inc(x_129);
x_130 = lean_ctor_get(x_112, 12);
lean_inc(x_130);
x_131 = lean_ctor_get(x_112, 13);
lean_inc(x_131);
x_132 = lean_ctor_get(x_112, 15);
lean_inc(x_132);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 lean_ctor_release(x_112, 4);
 lean_ctor_release(x_112, 5);
 lean_ctor_release(x_112, 6);
 lean_ctor_release(x_112, 7);
 lean_ctor_release(x_112, 8);
 lean_ctor_release(x_112, 9);
 lean_ctor_release(x_112, 10);
 lean_ctor_release(x_112, 11);
 lean_ctor_release(x_112, 12);
 lean_ctor_release(x_112, 13);
 lean_ctor_release(x_112, 14);
 lean_ctor_release(x_112, 15);
 x_133 = x_112;
} else {
 lean_dec_ref(x_112);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_113, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_113, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_113, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 x_137 = x_113;
} else {
 lean_dec_ref(x_113);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_114, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_114, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_114, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_114, 3);
lean_inc(x_141);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 x_142 = x_114;
} else {
 lean_dec_ref(x_114);
 x_142 = lean_box(0);
}
x_162 = lean_array_get_size(x_138);
x_163 = lean_nat_dec_lt(x_116, x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_dec(x_116);
x_143 = x_138;
goto block_161;
}
else
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_array_fget(x_138, x_116);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_166 = lean_ctor_get(x_164, 27);
x_167 = lean_box(0);
x_168 = lean_array_fset(x_138, x_116, x_167);
lean_inc(x_1);
x_169 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_166, x_1, x_167);
lean_ctor_set(x_164, 27, x_169);
x_170 = lean_array_fset(x_168, x_116, x_164);
lean_dec(x_116);
x_143 = x_170;
goto block_161;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_171 = lean_ctor_get(x_164, 0);
x_172 = lean_ctor_get(x_164, 1);
x_173 = lean_ctor_get(x_164, 2);
x_174 = lean_ctor_get(x_164, 3);
x_175 = lean_ctor_get(x_164, 4);
x_176 = lean_ctor_get(x_164, 5);
x_177 = lean_ctor_get(x_164, 6);
x_178 = lean_ctor_get(x_164, 7);
x_179 = lean_ctor_get(x_164, 8);
x_180 = lean_ctor_get(x_164, 9);
x_181 = lean_ctor_get(x_164, 10);
x_182 = lean_ctor_get(x_164, 11);
x_183 = lean_ctor_get(x_164, 12);
x_184 = lean_ctor_get(x_164, 13);
x_185 = lean_ctor_get(x_164, 14);
x_186 = lean_ctor_get(x_164, 15);
x_187 = lean_ctor_get(x_164, 16);
x_188 = lean_ctor_get(x_164, 17);
x_189 = lean_ctor_get(x_164, 18);
x_190 = lean_ctor_get(x_164, 19);
x_191 = lean_ctor_get(x_164, 20);
x_192 = lean_ctor_get(x_164, 21);
x_193 = lean_ctor_get(x_164, 22);
x_194 = lean_ctor_get(x_164, 23);
x_195 = lean_ctor_get(x_164, 24);
x_196 = lean_ctor_get(x_164, 25);
x_197 = lean_ctor_get(x_164, 26);
x_198 = lean_ctor_get_uint8(x_164, sizeof(void*)*28);
x_199 = lean_ctor_get(x_164, 27);
lean_inc(x_199);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_164);
x_200 = lean_box(0);
x_201 = lean_array_fset(x_138, x_116, x_200);
lean_inc(x_1);
x_202 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_recordSynthPendingFailure_spec__4___redArg(x_199, x_1, x_200);
x_203 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_203, 0, x_171);
lean_ctor_set(x_203, 1, x_172);
lean_ctor_set(x_203, 2, x_173);
lean_ctor_set(x_203, 3, x_174);
lean_ctor_set(x_203, 4, x_175);
lean_ctor_set(x_203, 5, x_176);
lean_ctor_set(x_203, 6, x_177);
lean_ctor_set(x_203, 7, x_178);
lean_ctor_set(x_203, 8, x_179);
lean_ctor_set(x_203, 9, x_180);
lean_ctor_set(x_203, 10, x_181);
lean_ctor_set(x_203, 11, x_182);
lean_ctor_set(x_203, 12, x_183);
lean_ctor_set(x_203, 13, x_184);
lean_ctor_set(x_203, 14, x_185);
lean_ctor_set(x_203, 15, x_186);
lean_ctor_set(x_203, 16, x_187);
lean_ctor_set(x_203, 17, x_188);
lean_ctor_set(x_203, 18, x_189);
lean_ctor_set(x_203, 19, x_190);
lean_ctor_set(x_203, 20, x_191);
lean_ctor_set(x_203, 21, x_192);
lean_ctor_set(x_203, 22, x_193);
lean_ctor_set(x_203, 23, x_194);
lean_ctor_set(x_203, 24, x_195);
lean_ctor_set(x_203, 25, x_196);
lean_ctor_set(x_203, 26, x_197);
lean_ctor_set(x_203, 27, x_202);
lean_ctor_set_uint8(x_203, sizeof(void*)*28, x_198);
x_204 = lean_array_fset(x_201, x_116, x_203);
lean_dec(x_116);
x_143 = x_204;
goto block_161;
}
}
block_54:
{
lean_object* x_39; 
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_1);
x_39 = l_Lean_Meta_Grind_mkDiseqProof(x_1, x_2, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3;
x_43 = lean_box(0);
if (lean_is_scalar(x_16)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_16;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_25);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Expr_const___override(x_42, x_44);
x_46 = l_Lean_mkApp4(x_45, x_24, x_28, x_1, x_40);
x_47 = lean_box(0);
x_48 = lean_unbox(x_47);
x_49 = l_Lean_Meta_Grind_pushEqCore(x_29, x_27, x_46, x_48, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_41);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
block_110:
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_1);
x_57 = l_Lean_Expr_app___override(x_56, x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_1);
x_61 = l_Lean_mkAppB(x_26, x_1, x_59);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_pre(x_61, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_63);
x_66 = lean_grind_internalize(x_63, x_14, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_66, 1);
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6;
x_71 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_70, x_10, x_68);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_free_object(x_66);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_29 = x_63;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_74;
goto block_54;
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_71, 1);
x_77 = lean_ctor_get(x_71, 0);
lean_dec(x_77);
x_78 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_63);
x_79 = l_Lean_MessageData_ofExpr(x_63);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_79);
lean_ctor_set(x_71, 0, x_78);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_78);
lean_ctor_set(x_66, 0, x_71);
x_80 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_70, x_66, x_8, x_9, x_10, x_11, x_76);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_29 = x_63;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_81;
goto block_54;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_dec(x_71);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_63);
x_84 = l_Lean_MessageData_ofExpr(x_63);
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_tag(x_66, 7);
lean_ctor_set(x_66, 1, x_83);
lean_ctor_set(x_66, 0, x_85);
x_86 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_70, x_66, x_8, x_9, x_10, x_11, x_82);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_29 = x_63;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_87;
goto block_54;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_66, 1);
lean_inc(x_88);
lean_dec(x_66);
x_89 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6;
x_90 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_89, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_29 = x_63;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_93;
goto block_54;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_63);
x_97 = l_Lean_MessageData_ofExpr(x_63);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(7, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 7);
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
x_100 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_89, x_99, x_8, x_9, x_10, x_11, x_94);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_29 = x_63;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_10;
x_37 = x_11;
x_38 = x_101;
goto block_54;
}
}
}
else
{
lean_dec(x_63);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_66;
}
}
else
{
uint8_t x_102; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_62);
if (x_102 == 0)
{
return x_62;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_62, 0);
x_104 = lean_ctor_get(x_62, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_62);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_58);
if (x_106 == 0)
{
return x_58;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_58, 0);
x_108 = lean_ctor_get(x_58, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_58);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
block_161:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 4, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_140);
lean_ctor_set(x_144, 3, x_141);
if (lean_is_scalar(x_137)) {
 x_145 = lean_alloc_ctor(0, 4, 0);
} else {
 x_145 = x_137;
}
lean_ctor_set(x_145, 0, x_134);
lean_ctor_set(x_145, 1, x_135);
lean_ctor_set(x_145, 2, x_144);
lean_ctor_set(x_145, 3, x_136);
if (lean_is_scalar(x_133)) {
 x_146 = lean_alloc_ctor(0, 16, 1);
} else {
 x_146 = x_133;
}
lean_ctor_set(x_146, 0, x_117);
lean_ctor_set(x_146, 1, x_118);
lean_ctor_set(x_146, 2, x_119);
lean_ctor_set(x_146, 3, x_120);
lean_ctor_set(x_146, 4, x_121);
lean_ctor_set(x_146, 5, x_122);
lean_ctor_set(x_146, 6, x_123);
lean_ctor_set(x_146, 7, x_124);
lean_ctor_set(x_146, 8, x_126);
lean_ctor_set(x_146, 9, x_127);
lean_ctor_set(x_146, 10, x_128);
lean_ctor_set(x_146, 11, x_129);
lean_ctor_set(x_146, 12, x_130);
lean_ctor_set(x_146, 13, x_131);
lean_ctor_set(x_146, 14, x_145);
lean_ctor_set(x_146, 15, x_132);
lean_ctor_set_uint8(x_146, sizeof(void*)*16, x_125);
x_147 = lean_st_ref_set(x_4, x_146, x_115);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_148);
lean_dec(x_3);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_150, 17);
lean_inc(x_151);
lean_dec(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10;
x_154 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_153);
x_55 = x_152;
x_56 = x_154;
goto block_110;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
lean_dec(x_149);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
x_55 = x_155;
x_56 = x_156;
goto block_110;
}
}
else
{
uint8_t x_157; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_149);
if (x_157 == 0)
{
return x_149;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_149, 0);
x_159 = lean_ctor_get(x_149, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_149);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
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
x_205 = !lean_is_exclusive(x_17);
if (x_205 == 0)
{
return x_17;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_17, 0);
x_207 = lean_ctor_get(x_17, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_17);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
LEAN_EXPORT lean_object* lean_process_ring_diseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_109; lean_object* x_110; 
lean_inc(x_2);
lean_inc(x_1);
x_109 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_inSameRing_x3f___redArg(x_1, x_2, x_3, x_11);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
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
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 0);
lean_dec(x_112);
x_113 = lean_box(0);
lean_ctor_set(x_109, 0, x_113);
return x_109;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
lean_dec(x_109);
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
lean_dec(x_110);
x_119 = l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0;
x_120 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_119, x_9, x_117);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_118);
x_126 = lean_unbox(x_124);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_126);
x_127 = lean_unbox(x_122);
lean_dec(x_122);
if (x_127 == 0)
{
lean_free_object(x_120);
x_46 = x_125;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_123;
goto block_108;
}
else
{
lean_object* x_128; 
x_128 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 1);
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_132 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_136 = l_Lean_mkNot(x_133);
x_137 = l_Lean_MessageData_ofExpr(x_136);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_137);
lean_ctor_set(x_128, 0, x_135);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_135);
lean_ctor_set(x_120, 0, x_128);
x_138 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_119, x_120, x_7, x_8, x_9, x_10, x_134);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_46 = x_125;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_139;
goto block_108;
}
else
{
uint8_t x_140; 
lean_free_object(x_128);
lean_dec(x_125);
lean_free_object(x_120);
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
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_128, 1);
lean_inc(x_144);
lean_dec(x_128);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_145 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_149 = l_Lean_mkNot(x_146);
x_150 = l_Lean_MessageData_ofExpr(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_148);
lean_ctor_set(x_120, 0, x_151);
x_152 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_119, x_120, x_7, x_8, x_9, x_10, x_147);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_46 = x_125;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_153;
goto block_108;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_125);
lean_free_object(x_120);
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
x_154 = lean_ctor_get(x_145, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_145, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_156 = x_145;
} else {
 lean_dec_ref(x_145);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
lean_dec(x_125);
lean_free_object(x_120);
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
return x_128;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_120, 0);
x_159 = lean_ctor_get(x_120, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_120);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_118);
x_162 = lean_unbox(x_160);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_162);
x_163 = lean_unbox(x_158);
lean_dec(x_158);
if (x_163 == 0)
{
x_46 = x_161;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_159;
goto block_108;
}
else
{
lean_object* x_164; 
x_164 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_159);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_166 = x_164;
} else {
 lean_dec_ref(x_164);
 x_166 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_167 = l_Lean_Meta_mkEq(x_1, x_2, x_7, x_8, x_9, x_10, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_171 = l_Lean_mkNot(x_168);
x_172 = l_Lean_MessageData_ofExpr(x_171);
if (lean_is_scalar(x_166)) {
 x_173 = lean_alloc_ctor(7, 2, 0);
} else {
 x_173 = x_166;
 lean_ctor_set_tag(x_173, 7);
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
x_175 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_119, x_174, x_7, x_8, x_9, x_10, x_169);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_46 = x_161;
x_47 = x_3;
x_48 = x_4;
x_49 = x_5;
x_50 = x_6;
x_51 = x_7;
x_52 = x_8;
x_53 = x_9;
x_54 = x_10;
x_55 = x_176;
goto block_108;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_166);
lean_dec(x_161);
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
x_177 = lean_ctor_get(x_167, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_167, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_179 = x_167;
} else {
 lean_dec_ref(x_167);
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
lean_dec(x_161);
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
return x_164;
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_32:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_18);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_16);
lean_ctor_set(x_30, 3, x_17);
lean_ctor_set(x_30, 4, x_29);
x_31 = l_Lean_Meta_Grind_Arith_CommRing_addNewDiseq(x_30, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_31;
}
block_45:
{
lean_object* x_43; 
x_43 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq(x_1, x_2, x_38, x_37, x_41, x_42, x_34, x_40, x_39, x_36, x_33, x_35);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_12 = x_44;
goto block_15;
}
else
{
return x_43;
}
}
block_108:
{
lean_object* x_56; 
lean_inc(x_1);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_1, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
lean_inc(x_2);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
lean_inc(x_75);
lean_inc(x_65);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_65);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Grind_CommRing_Expr_toPolyM(x_76, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_Grind_Arith_CommRing_isField(x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_16 = x_65;
x_17 = x_75;
x_18 = x_78;
x_19 = x_46;
x_20 = x_47;
x_21 = x_48;
x_22 = x_49;
x_23 = x_50;
x_24 = x_51;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_83;
goto block_32;
}
else
{
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_16 = x_65;
x_17 = x_75;
x_18 = x_78;
x_19 = x_46;
x_20 = x_47;
x_21 = x_48;
x_22 = x_49;
x_23 = x_50;
x_24 = x_51;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_84;
goto block_32;
}
else
{
lean_dec(x_78);
lean_dec(x_65);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
lean_dec(x_80);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_88 = lean_int_dec_eq(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
x_33 = x_54;
x_34 = x_50;
x_35 = x_85;
x_36 = x_53;
x_37 = x_47;
x_38 = x_46;
x_39 = x_52;
x_40 = x_51;
x_41 = x_48;
x_42 = x_49;
goto block_45;
}
else
{
lean_object* x_89; 
x_89 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq(x_1, x_2, x_46, x_47, x_48, x_49, x_50, x_51, x_52, x_53, x_54, x_85);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_12 = x_90;
goto block_15;
}
else
{
return x_89;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_75);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_dec(x_80);
x_33 = x_54;
x_34 = x_50;
x_35 = x_91;
x_36 = x_53;
x_37 = x_47;
x_38 = x_46;
x_39 = x_52;
x_40 = x_51;
x_41 = x_48;
x_42 = x_49;
goto block_45;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_80);
if (x_92 == 0)
{
return x_80;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_80, 0);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_80);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_77);
if (x_96 == 0)
{
return x_77;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_77, 0);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_77);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_66);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_66, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_66);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_56);
if (x_104 == 0)
{
return x_56;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_56, 0);
x_106 = lean_ctor_get(x_56, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_56);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(1);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*28);
lean_dec(x_23);
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_ctor_get_uint8(x_26, sizeof(void*)*28);
lean_dec(x_26);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
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
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_7, x_6);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_8, 1);
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
x_24 = lean_array_uget(x_5, x_7);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(x_1, x_2, x_3, x_24, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_8, 0, x_29);
lean_ctor_set(x_25, 0, x_8);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_8, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
lean_dec(x_22);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_34);
lean_ctor_set(x_8, 0, x_4);
x_35 = 1;
x_36 = lean_usize_add(x_7, x_35);
x_7 = x_36;
x_18 = x_33;
goto _start;
}
}
else
{
uint8_t x_38; 
lean_free_object(x_8);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_dec(x_8);
x_43 = lean_array_uget(x_5, x_7);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_42);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(x_1, x_2, x_3, x_43, x_42, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
lean_dec(x_42);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_52);
x_54 = 1;
x_55 = lean_usize_add(x_7, x_54);
x_7 = x_55;
x_8 = x_53;
x_18 = x_51;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_42);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_23 = lean_apply_12(x_1, x_22, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_6, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_20);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_32);
lean_ctor_set(x_6, 0, x_2);
x_33 = 1;
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_16 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_6);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_40);
x_42 = lean_apply_12(x_1, x_41, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_40);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
x_16 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_6);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_addNewDiseq(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_isInconsistent___redArg(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
lean_inc(x_2);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_array_size(x_17);
x_21 = 0;
x_22 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_18, x_17, x_20, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_27);
lean_ctor_set(x_22, 0, x_4);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_free_object(x_4);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_33);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_free_object(x_4);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
x_44 = lean_array_size(x_41);
x_45 = 0;
x_46 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_42, x_41, x_44, x_45, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_50 = x_46;
} else {
 lean_dec_ref(x_46);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_47);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_55 = x_46;
} else {
 lean_dec_ref(x_46);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_46, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_60 = x_46;
} else {
 lean_dec_ref(x_46);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_4);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_4, 0);
x_64 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0___boxed), 14, 2);
lean_closure_set(x_64, 0, x_1);
lean_closure_set(x_64, 1, x_2);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_5);
x_67 = lean_array_size(x_63);
x_68 = 0;
x_69 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(x_64, x_65, x_63, x_67, x_68, x_66, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_69, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_dec(x_70);
lean_ctor_set(x_4, 0, x_74);
lean_ctor_set(x_69, 0, x_4);
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
lean_ctor_set(x_4, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_70);
lean_free_object(x_4);
x_78 = !lean_is_exclusive(x_69);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_69, 0);
lean_dec(x_79);
x_80 = lean_ctor_get(x_71, 0);
lean_inc(x_80);
lean_dec(x_71);
lean_ctor_set(x_69, 0, x_80);
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_dec(x_69);
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
lean_dec(x_71);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_free_object(x_4);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
return x_69;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_69, 0);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_69);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_4, 0);
lean_inc(x_88);
lean_dec(x_4);
x_89 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0___boxed), 14, 2);
lean_closure_set(x_89, 0, x_1);
lean_closure_set(x_89, 1, x_2);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_5);
x_92 = lean_array_size(x_88);
x_93 = 0;
x_94 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(x_89, x_90, x_88, x_92, x_93, x_91, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_88);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_95);
x_102 = lean_ctor_get(x_94, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
lean_dec(x_96);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_94, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_94, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_108 = x_94;
} else {
 lean_dec_ref(x_94);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_23 = lean_apply_12(x_1, x_22, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_6, 0, x_29);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_20);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_2);
x_37 = 1;
x_38 = lean_usize_add(x_5, x_37);
x_5 = x_38;
x_16 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_6);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_dec(x_6);
x_45 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_44);
x_46 = lean_apply_12(x_1, x_45, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
lean_dec(x_44);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
lean_dec(x_47);
lean_inc(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_5, x_58);
x_5 = x_59;
x_6 = x_57;
x_16 = x_55;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_44);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_63 = x_46;
} else {
 lean_dec_ref(x_46);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_6);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_addNewDiseq(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Meta_Grind_isInconsistent___redArg(x_6, x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
lean_inc(x_2);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_2);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_17, 0, x_30);
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(x_1, x_2, x_4, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0___boxed), 14, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_array_size(x_16);
x_31 = 0;
x_32 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3(x_27, x_28, x_16, x_30, x_31, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_32, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_33);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_43);
return x_32;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_ctor_get(x_34, 0);
lean_inc(x_45);
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_32);
if (x_47 == 0)
{
return x_32;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_32, 0);
x_49 = lean_ctor_get(x_32, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_32);
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
uint8_t x_51; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1;
x_4 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_73; uint8_t x_74; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_take(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 14);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_12, 26);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 7);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_15, sizeof(void*)*16);
x_30 = lean_ctor_get(x_15, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 9);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 10);
lean_inc(x_32);
x_33 = lean_ctor_get(x_15, 11);
lean_inc(x_33);
x_34 = lean_ctor_get(x_15, 12);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 13);
lean_inc(x_35);
x_36 = lean_ctor_get(x_15, 15);
lean_inc(x_36);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 lean_ctor_release(x_15, 6);
 lean_ctor_release(x_15, 7);
 lean_ctor_release(x_15, 8);
 lean_ctor_release(x_15, 9);
 lean_ctor_release(x_15, 10);
 lean_ctor_release(x_15, 11);
 lean_ctor_release(x_15, 12);
 lean_ctor_release(x_15, 13);
 lean_ctor_release(x_15, 14);
 lean_ctor_release(x_15, 15);
 x_37 = x_15;
} else {
 lean_dec_ref(x_15);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_16, 3);
lean_inc(x_40);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 x_41 = x_16;
} else {
 lean_dec_ref(x_16);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_17, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_17, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_17, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 lean_ctor_release(x_17, 3);
 x_46 = x_17;
} else {
 lean_dec_ref(x_17);
 x_46 = lean_box(0);
}
x_73 = lean_array_get_size(x_42);
x_74 = lean_nat_dec_lt(x_20, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_dec(x_20);
x_47 = x_42;
goto block_72;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_array_fget(x_42, x_20);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_75, 26);
lean_dec(x_77);
x_78 = lean_box(0);
x_79 = lean_array_fset(x_42, x_20, x_78);
x_80 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3;
lean_ctor_set(x_75, 26, x_80);
x_81 = lean_array_fset(x_79, x_20, x_75);
lean_dec(x_20);
x_47 = x_81;
goto block_72;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_82 = lean_ctor_get(x_75, 0);
x_83 = lean_ctor_get(x_75, 1);
x_84 = lean_ctor_get(x_75, 2);
x_85 = lean_ctor_get(x_75, 3);
x_86 = lean_ctor_get(x_75, 4);
x_87 = lean_ctor_get(x_75, 5);
x_88 = lean_ctor_get(x_75, 6);
x_89 = lean_ctor_get(x_75, 7);
x_90 = lean_ctor_get(x_75, 8);
x_91 = lean_ctor_get(x_75, 9);
x_92 = lean_ctor_get(x_75, 10);
x_93 = lean_ctor_get(x_75, 11);
x_94 = lean_ctor_get(x_75, 12);
x_95 = lean_ctor_get(x_75, 13);
x_96 = lean_ctor_get(x_75, 14);
x_97 = lean_ctor_get(x_75, 15);
x_98 = lean_ctor_get(x_75, 16);
x_99 = lean_ctor_get(x_75, 17);
x_100 = lean_ctor_get(x_75, 18);
x_101 = lean_ctor_get(x_75, 19);
x_102 = lean_ctor_get(x_75, 20);
x_103 = lean_ctor_get(x_75, 21);
x_104 = lean_ctor_get(x_75, 22);
x_105 = lean_ctor_get(x_75, 23);
x_106 = lean_ctor_get(x_75, 24);
x_107 = lean_ctor_get(x_75, 25);
x_108 = lean_ctor_get_uint8(x_75, sizeof(void*)*28);
x_109 = lean_ctor_get(x_75, 27);
lean_inc(x_109);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_75);
x_110 = lean_box(0);
x_111 = lean_array_fset(x_42, x_20, x_110);
x_112 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3;
x_113 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_113, 0, x_82);
lean_ctor_set(x_113, 1, x_83);
lean_ctor_set(x_113, 2, x_84);
lean_ctor_set(x_113, 3, x_85);
lean_ctor_set(x_113, 4, x_86);
lean_ctor_set(x_113, 5, x_87);
lean_ctor_set(x_113, 6, x_88);
lean_ctor_set(x_113, 7, x_89);
lean_ctor_set(x_113, 8, x_90);
lean_ctor_set(x_113, 9, x_91);
lean_ctor_set(x_113, 10, x_92);
lean_ctor_set(x_113, 11, x_93);
lean_ctor_set(x_113, 12, x_94);
lean_ctor_set(x_113, 13, x_95);
lean_ctor_set(x_113, 14, x_96);
lean_ctor_set(x_113, 15, x_97);
lean_ctor_set(x_113, 16, x_98);
lean_ctor_set(x_113, 17, x_99);
lean_ctor_set(x_113, 18, x_100);
lean_ctor_set(x_113, 19, x_101);
lean_ctor_set(x_113, 20, x_102);
lean_ctor_set(x_113, 21, x_103);
lean_ctor_set(x_113, 22, x_104);
lean_ctor_set(x_113, 23, x_105);
lean_ctor_set(x_113, 24, x_106);
lean_ctor_set(x_113, 25, x_107);
lean_ctor_set(x_113, 26, x_112);
lean_ctor_set(x_113, 27, x_109);
lean_ctor_set_uint8(x_113, sizeof(void*)*28, x_108);
x_114 = lean_array_fset(x_111, x_20, x_113);
lean_dec(x_20);
x_47 = x_114;
goto block_72;
}
}
block_72:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 4, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set(x_48, 3, x_45);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_39);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_40);
if (lean_is_scalar(x_37)) {
 x_50 = lean_alloc_ctor(0, 16, 1);
} else {
 x_50 = x_37;
}
lean_ctor_set(x_50, 0, x_21);
lean_ctor_set(x_50, 1, x_22);
lean_ctor_set(x_50, 2, x_23);
lean_ctor_set(x_50, 3, x_24);
lean_ctor_set(x_50, 4, x_25);
lean_ctor_set(x_50, 5, x_26);
lean_ctor_set(x_50, 6, x_27);
lean_ctor_set(x_50, 7, x_28);
lean_ctor_set(x_50, 8, x_30);
lean_ctor_set(x_50, 9, x_31);
lean_ctor_set(x_50, 10, x_32);
lean_ctor_set(x_50, 11, x_33);
lean_ctor_set(x_50, 12, x_34);
lean_ctor_set(x_50, 13, x_35);
lean_ctor_set(x_50, 14, x_49);
lean_ctor_set(x_50, 15, x_36);
lean_ctor_set_uint8(x_50, sizeof(void*)*16, x_29);
x_51 = lean_st_ref_set(x_2, x_50, x_18);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0;
x_55 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(x_54, x_53, x_19, x_54, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_55, 0);
lean_dec(x_59);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_55, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_57, 0);
lean_inc(x_64);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_64);
return x_55;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_66 = lean_ctor_get(x_57, 0);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_55);
if (x_68 == 0)
{
return x_55;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_55, 0);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_55);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_11);
if (x_115 == 0)
{
return x_11;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_11, 0);
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_11);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0___boxed(lean_object** _args) {
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
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_19, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_5);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__3(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_int_dec_eq(x_11, x_13);
if (x_15 == 0)
{
x_7 = x_15;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Grind_CommRing_beqPoly____x40_Init_Grind_Ring_Poly___hyg_4125_(x_12, x_14);
x_7 = x_16;
goto block_10;
}
block_10:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_int_dec_eq(x_10, x_12);
if (x_14 == 0)
{
x_7 = x_14;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = l_Lean_Grind_CommRing_beqPoly____x40_Init_Grind_Ring_Poly___hyg_4125_(x_11, x_13);
x_7 = x_15;
goto block_9;
}
block_9:
{
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_29; uint8_t x_30; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_array_get_size(x_1);
x_29 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_30 = lean_int_dec_lt(x_7, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint64_t x_34; 
x_31 = lean_nat_abs(x_7);
lean_dec(x_7);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_mul(x_32, x_31);
lean_dec(x_31);
x_34 = lean_uint64_of_nat(x_33);
lean_dec(x_33);
x_10 = x_34;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; 
x_35 = lean_nat_abs(x_7);
lean_dec(x_7);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_35, x_36);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_37);
lean_dec(x_37);
x_40 = lean_nat_add(x_39, x_36);
lean_dec(x_39);
x_41 = lean_uint64_of_nat(x_40);
lean_dec(x_40);
x_10 = x_41;
goto block_28;
}
block_28:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = l_Lean_Grind_CommRing_hashPoly____x40_Init_Grind_Ring_Poly___hyg_4375_(x_8);
lean_dec(x_8);
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_1, x_23);
if (lean_is_scalar(x_6)) {
 x_25 = lean_alloc_ctor(1, 3, 0);
} else {
 x_25 = x_6;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_uset(x_1, x_23, x_25);
x_1 = x_26;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2_spec__2___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_int_dec_eq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_17;
goto block_12;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Grind_CommRing_beqPoly____x40_Init_Grind_Ring_Poly___hyg_4125_(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_8 = x_18;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_10 = lean_alloc_ctor(1, 3, 0);
} else {
 x_10 = x_7;
}
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(1, 3, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_6);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("impEq", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", noZeroDivisors: false", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("skip: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", k: ", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_111; size_t x_112; lean_object* x_113; lean_object* x_114; uint64_t x_115; lean_object* x_116; uint64_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint64_t x_121; lean_object* x_156; 
lean_inc(x_3);
x_156 = l_Lean_Grind_CommRing_Expr_toPolyM(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_157);
x_160 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_159, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; uint64_t x_172; uint64_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; size_t x_290; lean_object* x_291; lean_object* x_292; uint64_t x_293; uint64_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_314; size_t x_315; lean_object* x_316; uint64_t x_317; uint64_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_323; size_t x_324; lean_object* x_325; uint64_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint64_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint64_t x_360; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_690; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1;
x_164 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_163, x_11, x_162);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_getMultiplier(x_161);
x_690 = lean_unbox(x_165);
lean_dec(x_165);
if (x_690 == 0)
{
x_662 = x_4;
x_663 = x_5;
x_664 = x_6;
x_665 = x_7;
x_666 = x_8;
x_667 = x_9;
x_668 = x_10;
x_669 = x_11;
x_670 = x_12;
x_671 = x_166;
goto block_673;
}
else
{
lean_object* x_691; 
x_691 = l_Lean_Meta_Grind_updateLastTag(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_166);
if (lean_obj_tag(x_691) == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_719; 
x_692 = lean_ctor_get(x_691, 1);
lean_inc(x_692);
lean_dec(x_691);
x_719 = lean_ctor_get(x_161, 0);
lean_inc(x_719);
x_693 = x_719;
goto block_718;
block_718:
{
lean_object* x_694; 
x_694 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_693, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_692);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
lean_inc(x_2);
x_698 = l_Lean_MessageData_ofExpr(x_2);
x_699 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
x_700 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4;
x_701 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
x_702 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_703 = lean_int_dec_lt(x_168, x_702);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; 
x_704 = lean_nat_abs(x_168);
x_705 = l_Nat_reprFast(x_704);
x_674 = x_695;
x_675 = x_696;
x_676 = x_697;
x_677 = x_700;
x_678 = x_701;
x_679 = x_705;
goto block_689;
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_706 = lean_nat_abs(x_168);
x_707 = lean_unsigned_to_nat(1u);
x_708 = lean_nat_sub(x_706, x_707);
lean_dec(x_706);
x_709 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_710 = lean_unsigned_to_nat(1u);
x_711 = lean_nat_add(x_708, x_710);
lean_dec(x_708);
x_712 = l_Nat_reprFast(x_711);
x_713 = lean_string_append(x_709, x_712);
lean_dec(x_712);
x_674 = x_695;
x_675 = x_696;
x_676 = x_697;
x_677 = x_700;
x_678 = x_701;
x_679 = x_713;
goto block_689;
}
}
else
{
uint8_t x_714; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_11);
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
x_714 = !lean_is_exclusive(x_694);
if (x_714 == 0)
{
return x_694;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_694, 0);
x_716 = lean_ctor_get(x_694, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_694);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_161);
lean_dec(x_12);
lean_dec(x_11);
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
x_720 = !lean_is_exclusive(x_691);
if (x_720 == 0)
{
return x_691;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_691, 0);
x_722 = lean_ctor_get(x_691, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_691);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
block_192:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_175);
lean_inc(x_168);
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_167;
}
lean_ctor_set(x_176, 0, x_168);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_2);
lean_ctor_set(x_177, 1, x_3);
x_178 = lean_array_get_size(x_170);
x_179 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_180 = lean_int_dec_lt(x_168, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint64_t x_184; 
x_181 = lean_nat_abs(x_168);
lean_dec(x_168);
x_182 = lean_unsigned_to_nat(2u);
x_183 = lean_nat_mul(x_182, x_181);
lean_dec(x_181);
x_184 = lean_uint64_of_nat(x_183);
lean_dec(x_183);
x_14 = x_170;
x_15 = x_169;
x_16 = x_171;
x_17 = x_178;
x_18 = x_172;
x_19 = x_176;
x_20 = x_173;
x_21 = x_177;
x_22 = x_175;
x_23 = x_174;
x_24 = x_184;
goto block_58;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint64_t x_191; 
x_185 = lean_nat_abs(x_168);
lean_dec(x_168);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_sub(x_185, x_186);
lean_dec(x_185);
x_188 = lean_unsigned_to_nat(2u);
x_189 = lean_nat_mul(x_188, x_187);
lean_dec(x_187);
x_190 = lean_nat_add(x_189, x_186);
lean_dec(x_189);
x_191 = lean_uint64_of_nat(x_190);
lean_dec(x_190);
x_14 = x_170;
x_15 = x_169;
x_16 = x_171;
x_17 = x_178;
x_18 = x_172;
x_19 = x_176;
x_20 = x_173;
x_21 = x_177;
x_22 = x_175;
x_23 = x_174;
x_24 = x_191;
goto block_58;
}
}
block_289:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2;
x_208 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_207, x_204, x_206);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_object* x_211; 
lean_dec(x_196);
lean_dec(x_168);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_59 = x_193;
x_60 = x_194;
x_61 = x_195;
x_62 = x_197;
x_63 = x_198;
x_64 = x_199;
x_65 = x_200;
x_66 = x_201;
x_67 = x_202;
x_68 = x_203;
x_69 = x_204;
x_70 = x_205;
x_71 = x_211;
goto block_81;
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_208);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_208, 1);
x_214 = lean_ctor_get(x_208, 0);
lean_dec(x_214);
x_215 = l_Lean_Meta_Grind_updateLastTag(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_193);
lean_inc(x_2);
x_217 = l_Lean_Meta_mkEq(x_2, x_193, x_202, x_203, x_204, x_205, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_224 = l_Lean_MessageData_ofExpr(x_218);
lean_ctor_set_tag(x_208, 7);
lean_ctor_set(x_208, 1, x_224);
lean_ctor_set(x_208, 0, x_223);
x_225 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4;
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_208);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_228 = lean_int_dec_lt(x_168, x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_abs(x_168);
lean_dec(x_168);
x_230 = l_Nat_reprFast(x_229);
x_82 = x_225;
x_83 = x_207;
x_84 = x_222;
x_85 = x_197;
x_86 = x_199;
x_87 = x_202;
x_88 = x_195;
x_89 = x_203;
x_90 = x_226;
x_91 = x_193;
x_92 = x_198;
x_93 = x_200;
x_94 = x_204;
x_95 = x_201;
x_96 = x_205;
x_97 = x_194;
x_98 = x_221;
x_99 = x_223;
x_100 = x_230;
goto block_110;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_231 = lean_nat_abs(x_168);
lean_dec(x_168);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_sub(x_231, x_232);
lean_dec(x_231);
x_234 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_add(x_233, x_235);
lean_dec(x_233);
x_237 = l_Nat_reprFast(x_236);
x_238 = lean_string_append(x_234, x_237);
lean_dec(x_237);
x_82 = x_225;
x_83 = x_207;
x_84 = x_222;
x_85 = x_197;
x_86 = x_199;
x_87 = x_202;
x_88 = x_195;
x_89 = x_203;
x_90 = x_226;
x_91 = x_193;
x_92 = x_198;
x_93 = x_200;
x_94 = x_204;
x_95 = x_201;
x_96 = x_205;
x_97 = x_194;
x_98 = x_221;
x_99 = x_223;
x_100 = x_238;
goto block_110;
}
}
else
{
uint8_t x_239; 
lean_dec(x_218);
lean_free_object(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_220);
if (x_239 == 0)
{
return x_220;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_220, 0);
x_241 = lean_ctor_get(x_220, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_220);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
uint8_t x_243; 
lean_free_object(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_217);
if (x_243 == 0)
{
return x_217;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_217, 0);
x_245 = lean_ctor_get(x_217, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_217);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_free_object(x_208);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_215);
if (x_247 == 0)
{
return x_215;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_215, 0);
x_249 = lean_ctor_get(x_215, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_215);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_208, 1);
lean_inc(x_251);
lean_dec(x_208);
x_252 = l_Lean_Meta_Grind_updateLastTag(x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_inc(x_193);
lean_inc(x_2);
x_254 = l_Lean_Meta_mkEq(x_2, x_193, x_202, x_203, x_204, x_205, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = l_Lean_Grind_CommRing_Poly_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_getPolyConst_spec__0(x_196, x_197, x_198, x_199, x_200, x_201, x_202, x_203, x_204, x_205, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_261 = l_Lean_MessageData_ofExpr(x_255);
x_262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4;
x_264 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_266 = lean_int_dec_lt(x_168, x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_nat_abs(x_168);
lean_dec(x_168);
x_268 = l_Nat_reprFast(x_267);
x_82 = x_263;
x_83 = x_207;
x_84 = x_259;
x_85 = x_197;
x_86 = x_199;
x_87 = x_202;
x_88 = x_195;
x_89 = x_203;
x_90 = x_264;
x_91 = x_193;
x_92 = x_198;
x_93 = x_200;
x_94 = x_204;
x_95 = x_201;
x_96 = x_205;
x_97 = x_194;
x_98 = x_258;
x_99 = x_260;
x_100 = x_268;
goto block_110;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = lean_nat_abs(x_168);
lean_dec(x_168);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_sub(x_269, x_270);
lean_dec(x_269);
x_272 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_271, x_273);
lean_dec(x_271);
x_275 = l_Nat_reprFast(x_274);
x_276 = lean_string_append(x_272, x_275);
lean_dec(x_275);
x_82 = x_263;
x_83 = x_207;
x_84 = x_259;
x_85 = x_197;
x_86 = x_199;
x_87 = x_202;
x_88 = x_195;
x_89 = x_203;
x_90 = x_264;
x_91 = x_193;
x_92 = x_198;
x_93 = x_200;
x_94 = x_204;
x_95 = x_201;
x_96 = x_205;
x_97 = x_194;
x_98 = x_258;
x_99 = x_260;
x_100 = x_276;
goto block_110;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_255);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = lean_ctor_get(x_257, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_257, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_279 = x_257;
} else {
 lean_dec_ref(x_257);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_ctor_get(x_254, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_254, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_283 = x_254;
} else {
 lean_dec_ref(x_254);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_285 = lean_ctor_get(x_252, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_252, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_287 = x_252;
} else {
 lean_dec_ref(x_252);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
}
block_313:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
lean_inc(x_296);
lean_inc(x_168);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_168);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_2);
lean_ctor_set(x_298, 1, x_3);
x_299 = lean_array_get_size(x_291);
x_300 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_301 = lean_int_dec_lt(x_168, x_300);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint64_t x_305; 
x_302 = lean_nat_abs(x_168);
lean_dec(x_168);
x_303 = lean_unsigned_to_nat(2u);
x_304 = lean_nat_mul(x_303, x_302);
lean_dec(x_302);
x_305 = lean_uint64_of_nat(x_304);
lean_dec(x_304);
x_111 = x_291;
x_112 = x_290;
x_113 = x_292;
x_114 = x_298;
x_115 = x_293;
x_116 = x_299;
x_117 = x_294;
x_118 = x_295;
x_119 = x_297;
x_120 = x_296;
x_121 = x_305;
goto block_155;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint64_t x_312; 
x_306 = lean_nat_abs(x_168);
lean_dec(x_168);
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_sub(x_306, x_307);
lean_dec(x_306);
x_309 = lean_unsigned_to_nat(2u);
x_310 = lean_nat_mul(x_309, x_308);
lean_dec(x_308);
x_311 = lean_nat_add(x_310, x_307);
lean_dec(x_310);
x_312 = lean_uint64_of_nat(x_311);
lean_dec(x_311);
x_111 = x_291;
x_112 = x_290;
x_113 = x_292;
x_114 = x_298;
x_115 = x_293;
x_116 = x_299;
x_117 = x_294;
x_118 = x_295;
x_119 = x_297;
x_120 = x_296;
x_121 = x_312;
goto block_155;
}
}
block_322:
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
x_290 = x_315;
x_291 = x_314;
x_292 = x_316;
x_293 = x_317;
x_294 = x_318;
x_295 = x_320;
x_296 = x_321;
goto block_313;
}
block_344:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_337, 0, x_336);
x_338 = l_Lean_MessageData_ofFormat(x_337);
x_339 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_339, 0, x_325);
lean_ctor_set(x_339, 1, x_338);
x_340 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7;
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_328, x_341, x_331, x_333, x_335, x_329, x_330);
lean_dec(x_329);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_331);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_314 = x_323;
x_315 = x_324;
x_316 = x_332;
x_317 = x_334;
x_318 = x_326;
x_319 = x_327;
x_320 = x_343;
goto block_322;
}
block_632:
{
uint64_t x_361; uint64_t x_362; uint64_t x_363; uint64_t x_364; uint64_t x_365; uint64_t x_366; uint64_t x_367; uint64_t x_368; size_t x_369; size_t x_370; size_t x_371; size_t x_372; size_t x_373; lean_object* x_374; lean_object* x_375; 
x_361 = l_Lean_Grind_CommRing_hashPoly____x40_Init_Grind_Ring_Poly___hyg_4375_(x_357);
lean_dec(x_357);
x_362 = lean_uint64_mix_hash(x_360, x_361);
x_363 = 32;
x_364 = lean_uint64_shift_right(x_362, x_363);
x_365 = lean_uint64_xor(x_362, x_364);
x_366 = 16;
x_367 = lean_uint64_shift_right(x_365, x_366);
x_368 = lean_uint64_xor(x_365, x_367);
x_369 = lean_uint64_to_usize(x_368);
x_370 = lean_usize_of_nat(x_358);
lean_dec(x_358);
x_371 = 1;
x_372 = lean_usize_sub(x_370, x_371);
x_373 = lean_usize_land(x_369, x_372);
x_374 = lean_array_uget(x_346, x_373);
x_375 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg(x_355, x_374);
lean_dec(x_374);
lean_dec(x_355);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; 
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_1);
x_376 = lean_ctor_get(x_161, 0);
lean_inc(x_376);
lean_dec(x_161);
x_169 = x_371;
x_170 = x_346;
x_171 = x_351;
x_172 = x_366;
x_173 = x_363;
x_174 = x_359;
x_175 = x_376;
goto block_192;
}
else
{
uint8_t x_377; 
lean_dec(x_167);
lean_dec(x_161);
x_377 = !lean_is_exclusive(x_375);
if (x_377 == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_375, 0);
x_379 = !lean_is_exclusive(x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_380 = lean_ctor_get(x_378, 0);
x_381 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_inc(x_2);
x_382 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_380, x_352, x_359);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
lean_inc(x_381);
lean_inc(x_3);
lean_ctor_set_tag(x_378, 4);
lean_ctor_set(x_378, 0, x_3);
x_386 = l_Lean_Grind_CommRing_Expr_toPolyM(x_378, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_385);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_inc(x_387);
lean_ctor_set_tag(x_375, 0);
lean_ctor_set(x_375, 0, x_387);
x_389 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_375, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_getMultiplier(x_390);
x_393 = lean_unsigned_to_nat(1u);
x_394 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
x_395 = lean_int_dec_eq(x_392, x_394);
lean_dec(x_392);
if (x_395 == 0)
{
lean_object* x_396; 
x_396 = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_391);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
lean_dec(x_387);
lean_dec(x_381);
lean_dec(x_350);
lean_dec(x_1);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_dec(x_396);
x_400 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2;
x_401 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_400, x_356, x_399);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_unbox(x_402);
lean_dec(x_402);
if (x_403 == 0)
{
lean_object* x_404; 
lean_dec(x_380);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_314 = x_346;
x_315 = x_371;
x_316 = x_351;
x_317 = x_366;
x_318 = x_363;
x_319 = x_390;
x_320 = x_404;
goto block_322;
}
else
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_401);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_401, 1);
x_407 = lean_ctor_get(x_401, 0);
lean_dec(x_407);
x_408 = l_Lean_Meta_Grind_updateLastTag(x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_406);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_352);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
lean_inc(x_349);
lean_inc(x_356);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_2);
x_410 = l_Lean_Meta_mkEq(x_2, x_380, x_353, x_354, x_356, x_349, x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9;
x_414 = l_Lean_MessageData_ofExpr(x_411);
lean_ctor_set_tag(x_401, 7);
lean_ctor_set(x_401, 1, x_414);
lean_ctor_set(x_401, 0, x_413);
x_415 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11;
x_416 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_416, 0, x_401);
lean_ctor_set(x_416, 1, x_415);
x_417 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_418 = lean_int_dec_lt(x_168, x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_nat_abs(x_168);
x_420 = l_Nat_reprFast(x_419);
x_323 = x_346;
x_324 = x_371;
x_325 = x_416;
x_326 = x_363;
x_327 = x_390;
x_328 = x_400;
x_329 = x_349;
x_330 = x_412;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_420;
goto block_344;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_421 = lean_nat_abs(x_168);
x_422 = lean_nat_sub(x_421, x_393);
lean_dec(x_421);
x_423 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_424 = lean_unsigned_to_nat(1u);
x_425 = lean_nat_add(x_422, x_424);
lean_dec(x_422);
x_426 = l_Nat_reprFast(x_425);
x_427 = lean_string_append(x_423, x_426);
lean_dec(x_426);
x_323 = x_346;
x_324 = x_371;
x_325 = x_416;
x_326 = x_363;
x_327 = x_390;
x_328 = x_400;
x_329 = x_349;
x_330 = x_412;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_427;
goto block_344;
}
}
else
{
uint8_t x_428; 
lean_free_object(x_401);
lean_dec(x_390);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_428 = !lean_is_exclusive(x_410);
if (x_428 == 0)
{
return x_410;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_410, 0);
x_430 = lean_ctor_get(x_410, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_410);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
else
{
uint8_t x_432; 
lean_free_object(x_401);
lean_dec(x_390);
lean_dec(x_380);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_432 = !lean_is_exclusive(x_408);
if (x_432 == 0)
{
return x_408;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_408, 0);
x_434 = lean_ctor_get(x_408, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_408);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
return x_435;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_401, 1);
lean_inc(x_436);
lean_dec(x_401);
x_437 = l_Lean_Meta_Grind_updateLastTag(x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_436);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_352);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
lean_dec(x_437);
lean_inc(x_349);
lean_inc(x_356);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_2);
x_439 = l_Lean_Meta_mkEq(x_2, x_380, x_353, x_354, x_356, x_349, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
x_442 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9;
x_443 = l_Lean_MessageData_ofExpr(x_440);
x_444 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_445 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11;
x_446 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_448 = lean_int_dec_lt(x_168, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; 
x_449 = lean_nat_abs(x_168);
x_450 = l_Nat_reprFast(x_449);
x_323 = x_346;
x_324 = x_371;
x_325 = x_446;
x_326 = x_363;
x_327 = x_390;
x_328 = x_400;
x_329 = x_349;
x_330 = x_441;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_450;
goto block_344;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_451 = lean_nat_abs(x_168);
x_452 = lean_nat_sub(x_451, x_393);
lean_dec(x_451);
x_453 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_454 = lean_unsigned_to_nat(1u);
x_455 = lean_nat_add(x_452, x_454);
lean_dec(x_452);
x_456 = l_Nat_reprFast(x_455);
x_457 = lean_string_append(x_453, x_456);
lean_dec(x_456);
x_323 = x_346;
x_324 = x_371;
x_325 = x_446;
x_326 = x_363;
x_327 = x_390;
x_328 = x_400;
x_329 = x_349;
x_330 = x_441;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_457;
goto block_344;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_390);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_458 = lean_ctor_get(x_439, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_439, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 lean_ctor_release(x_439, 1);
 x_460 = x_439;
} else {
 lean_dec_ref(x_439);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 2, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_390);
lean_dec(x_380);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_462 = lean_ctor_get(x_437, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_437, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_464 = x_437;
} else {
 lean_dec_ref(x_437);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
}
}
else
{
lean_object* x_466; 
lean_dec(x_351);
lean_dec(x_346);
x_466 = lean_ctor_get(x_396, 1);
lean_inc(x_466);
lean_dec(x_396);
x_193 = x_380;
x_194 = x_381;
x_195 = x_390;
x_196 = x_387;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_466;
goto block_289;
}
}
else
{
uint8_t x_467; 
lean_dec(x_390);
lean_dec(x_387);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_467 = !lean_is_exclusive(x_396);
if (x_467 == 0)
{
return x_396;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_396, 0);
x_469 = lean_ctor_get(x_396, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_396);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
else
{
lean_dec(x_351);
lean_dec(x_346);
x_193 = x_380;
x_194 = x_381;
x_195 = x_390;
x_196 = x_387;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_391;
goto block_289;
}
}
else
{
uint8_t x_471; 
lean_dec(x_387);
lean_dec(x_381);
lean_dec(x_380);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_471 = !lean_is_exclusive(x_389);
if (x_471 == 0)
{
return x_389;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_389, 0);
x_473 = lean_ctor_get(x_389, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_389);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_381);
lean_dec(x_380);
lean_free_object(x_375);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_386);
if (x_475 == 0)
{
return x_386;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_386, 0);
x_477 = lean_ctor_get(x_386, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_386);
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
lean_free_object(x_378);
lean_dec(x_381);
lean_dec(x_380);
lean_free_object(x_375);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_479 = !lean_is_exclusive(x_382);
if (x_479 == 0)
{
lean_object* x_480; 
x_480 = lean_ctor_get(x_382, 0);
lean_dec(x_480);
lean_ctor_set(x_382, 0, x_1);
return x_382;
}
else
{
lean_object* x_481; lean_object* x_482; 
x_481 = lean_ctor_get(x_382, 1);
lean_inc(x_481);
lean_dec(x_382);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_1);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_483 = lean_ctor_get(x_378, 0);
x_484 = lean_ctor_get(x_378, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_378);
lean_inc(x_483);
lean_inc(x_2);
x_485 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_483, x_352, x_359);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_unbox(x_486);
lean_dec(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
lean_dec(x_485);
lean_inc(x_484);
lean_inc(x_3);
x_489 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_489, 0, x_3);
lean_ctor_set(x_489, 1, x_484);
x_490 = l_Lean_Grind_CommRing_Expr_toPolyM(x_489, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_488);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
lean_dec(x_490);
lean_inc(x_491);
lean_ctor_set_tag(x_375, 0);
lean_ctor_set(x_375, 0, x_491);
x_493 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_375, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
x_496 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_getMultiplier(x_494);
x_497 = lean_unsigned_to_nat(1u);
x_498 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
x_499 = lean_int_dec_eq(x_496, x_498);
lean_dec(x_496);
if (x_499 == 0)
{
lean_object* x_500; 
x_500 = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_495);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; uint8_t x_502; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_unbox(x_501);
lean_dec(x_501);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; 
lean_dec(x_491);
lean_dec(x_484);
lean_dec(x_350);
lean_dec(x_1);
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
lean_dec(x_500);
x_504 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2;
x_505 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_504, x_356, x_503);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_unbox(x_506);
lean_dec(x_506);
if (x_507 == 0)
{
lean_object* x_508; 
lean_dec(x_483);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
x_508 = lean_ctor_get(x_505, 1);
lean_inc(x_508);
lean_dec(x_505);
x_314 = x_346;
x_315 = x_371;
x_316 = x_351;
x_317 = x_366;
x_318 = x_363;
x_319 = x_494;
x_320 = x_508;
goto block_322;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_505, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_510 = x_505;
} else {
 lean_dec_ref(x_505);
 x_510 = lean_box(0);
}
x_511 = l_Lean_Meta_Grind_updateLastTag(x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_509);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_352);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
lean_inc(x_349);
lean_inc(x_356);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_2);
x_513 = l_Lean_Meta_mkEq(x_2, x_483, x_353, x_354, x_356, x_349, x_512);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_516 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9;
x_517 = l_Lean_MessageData_ofExpr(x_514);
if (lean_is_scalar(x_510)) {
 x_518 = lean_alloc_ctor(7, 2, 0);
} else {
 x_518 = x_510;
 lean_ctor_set_tag(x_518, 7);
}
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
x_519 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11;
x_520 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_522 = lean_int_dec_lt(x_168, x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_nat_abs(x_168);
x_524 = l_Nat_reprFast(x_523);
x_323 = x_346;
x_324 = x_371;
x_325 = x_520;
x_326 = x_363;
x_327 = x_494;
x_328 = x_504;
x_329 = x_349;
x_330 = x_515;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_524;
goto block_344;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_525 = lean_nat_abs(x_168);
x_526 = lean_nat_sub(x_525, x_497);
lean_dec(x_525);
x_527 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_528 = lean_unsigned_to_nat(1u);
x_529 = lean_nat_add(x_526, x_528);
lean_dec(x_526);
x_530 = l_Nat_reprFast(x_529);
x_531 = lean_string_append(x_527, x_530);
lean_dec(x_530);
x_323 = x_346;
x_324 = x_371;
x_325 = x_520;
x_326 = x_363;
x_327 = x_494;
x_328 = x_504;
x_329 = x_349;
x_330 = x_515;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_531;
goto block_344;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_510);
lean_dec(x_494);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_532 = lean_ctor_get(x_513, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_513, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_534 = x_513;
} else {
 lean_dec_ref(x_513);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 2, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_533);
return x_535;
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_510);
lean_dec(x_494);
lean_dec(x_483);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_536 = lean_ctor_get(x_511, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_511, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_538 = x_511;
} else {
 lean_dec_ref(x_511);
 x_538 = lean_box(0);
}
if (lean_is_scalar(x_538)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_538;
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
return x_539;
}
}
}
else
{
lean_object* x_540; 
lean_dec(x_351);
lean_dec(x_346);
x_540 = lean_ctor_get(x_500, 1);
lean_inc(x_540);
lean_dec(x_500);
x_193 = x_483;
x_194 = x_484;
x_195 = x_494;
x_196 = x_491;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_540;
goto block_289;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_494);
lean_dec(x_491);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_541 = lean_ctor_get(x_500, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_500, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_543 = x_500;
} else {
 lean_dec_ref(x_500);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
return x_544;
}
}
else
{
lean_dec(x_351);
lean_dec(x_346);
x_193 = x_483;
x_194 = x_484;
x_195 = x_494;
x_196 = x_491;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_495;
goto block_289;
}
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_491);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_545 = lean_ctor_get(x_493, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_493, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_547 = x_493;
} else {
 lean_dec_ref(x_493);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_484);
lean_dec(x_483);
lean_free_object(x_375);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_549 = lean_ctor_get(x_490, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_490, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_551 = x_490;
} else {
 lean_dec_ref(x_490);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_484);
lean_dec(x_483);
lean_free_object(x_375);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_553 = lean_ctor_get(x_485, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_554 = x_485;
} else {
 lean_dec_ref(x_485);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(0, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_1);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_556 = lean_ctor_get(x_375, 0);
lean_inc(x_556);
lean_dec(x_375);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
lean_inc(x_557);
lean_inc(x_2);
x_560 = l_Lean_Meta_Grind_isEqv___redArg(x_2, x_557, x_352, x_359);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_unbox(x_561);
lean_dec(x_561);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
lean_inc(x_558);
lean_inc(x_3);
if (lean_is_scalar(x_559)) {
 x_564 = lean_alloc_ctor(4, 2, 0);
} else {
 x_564 = x_559;
 lean_ctor_set_tag(x_564, 4);
}
lean_ctor_set(x_564, 0, x_3);
lean_ctor_set(x_564, 1, x_558);
x_565 = l_Lean_Grind_CommRing_Expr_toPolyM(x_564, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_563);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_566 = lean_ctor_get(x_565, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_565, 1);
lean_inc(x_567);
lean_dec(x_565);
lean_inc(x_566);
x_568 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_568, 0, x_566);
x_569 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify(x_568, x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_567);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_getMultiplier(x_570);
x_573 = lean_unsigned_to_nat(1u);
x_574 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0;
x_575 = lean_int_dec_eq(x_572, x_574);
lean_dec(x_572);
if (x_575 == 0)
{
lean_object* x_576; 
x_576 = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(x_350, x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_571);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; uint8_t x_578; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
x_578 = lean_unbox(x_577);
lean_dec(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
lean_dec(x_566);
lean_dec(x_558);
lean_dec(x_350);
lean_dec(x_1);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_dec(x_576);
x_580 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2;
x_581 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_580, x_356, x_579);
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_unbox(x_582);
lean_dec(x_582);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_314 = x_346;
x_315 = x_371;
x_316 = x_351;
x_317 = x_366;
x_318 = x_363;
x_319 = x_570;
x_320 = x_584;
goto block_322;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_581, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_586 = x_581;
} else {
 lean_dec_ref(x_581);
 x_586 = lean_box(0);
}
x_587 = l_Lean_Meta_Grind_updateLastTag(x_352, x_345, x_347, x_348, x_353, x_354, x_356, x_349, x_585);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_352);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; 
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
lean_dec(x_587);
lean_inc(x_349);
lean_inc(x_356);
lean_inc(x_354);
lean_inc(x_353);
lean_inc(x_2);
x_589 = l_Lean_Meta_mkEq(x_2, x_557, x_353, x_354, x_356, x_349, x_588);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
x_592 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9;
x_593 = l_Lean_MessageData_ofExpr(x_590);
if (lean_is_scalar(x_586)) {
 x_594 = lean_alloc_ctor(7, 2, 0);
} else {
 x_594 = x_586;
 lean_ctor_set_tag(x_594, 7);
}
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
x_595 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11;
x_596 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_595);
x_597 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_598 = lean_int_dec_lt(x_168, x_597);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; 
x_599 = lean_nat_abs(x_168);
x_600 = l_Nat_reprFast(x_599);
x_323 = x_346;
x_324 = x_371;
x_325 = x_596;
x_326 = x_363;
x_327 = x_570;
x_328 = x_580;
x_329 = x_349;
x_330 = x_591;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_600;
goto block_344;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_601 = lean_nat_abs(x_168);
x_602 = lean_nat_sub(x_601, x_573);
lean_dec(x_601);
x_603 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5;
x_604 = lean_unsigned_to_nat(1u);
x_605 = lean_nat_add(x_602, x_604);
lean_dec(x_602);
x_606 = l_Nat_reprFast(x_605);
x_607 = lean_string_append(x_603, x_606);
lean_dec(x_606);
x_323 = x_346;
x_324 = x_371;
x_325 = x_596;
x_326 = x_363;
x_327 = x_570;
x_328 = x_580;
x_329 = x_349;
x_330 = x_591;
x_331 = x_353;
x_332 = x_351;
x_333 = x_354;
x_334 = x_366;
x_335 = x_356;
x_336 = x_607;
goto block_344;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_586);
lean_dec(x_570);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_608 = lean_ctor_get(x_589, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_589, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_610 = x_589;
} else {
 lean_dec_ref(x_589);
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
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_586);
lean_dec(x_570);
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_351);
lean_dec(x_349);
lean_dec(x_346);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_612 = lean_ctor_get(x_587, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_587, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_614 = x_587;
} else {
 lean_dec_ref(x_587);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_612);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
}
}
else
{
lean_object* x_616; 
lean_dec(x_351);
lean_dec(x_346);
x_616 = lean_ctor_get(x_576, 1);
lean_inc(x_616);
lean_dec(x_576);
x_193 = x_557;
x_194 = x_558;
x_195 = x_570;
x_196 = x_566;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_616;
goto block_289;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_570);
lean_dec(x_566);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_617 = lean_ctor_get(x_576, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_576, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_619 = x_576;
} else {
 lean_dec_ref(x_576);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 2, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_618);
return x_620;
}
}
else
{
lean_dec(x_351);
lean_dec(x_346);
x_193 = x_557;
x_194 = x_558;
x_195 = x_570;
x_196 = x_566;
x_197 = x_350;
x_198 = x_352;
x_199 = x_345;
x_200 = x_347;
x_201 = x_348;
x_202 = x_353;
x_203 = x_354;
x_204 = x_356;
x_205 = x_349;
x_206 = x_571;
goto block_289;
}
}
else
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_566);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_621 = lean_ctor_get(x_569, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_569, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 lean_ctor_release(x_569, 1);
 x_623 = x_569;
} else {
 lean_dec_ref(x_569);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 2, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_621);
lean_ctor_set(x_624, 1, x_622);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_625 = lean_ctor_get(x_565, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_565, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_565)) {
 lean_ctor_release(x_565, 0);
 lean_ctor_release(x_565, 1);
 x_627 = x_565;
} else {
 lean_dec_ref(x_565);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_356);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_345);
lean_dec(x_168);
lean_dec(x_3);
lean_dec(x_2);
x_629 = lean_ctor_get(x_560, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_630 = x_560;
} else {
 lean_dec_ref(x_560);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_1);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
}
}
}
block_661:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_644 = lean_ctor_get(x_1, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_1, 1);
lean_inc(x_645);
lean_inc(x_643);
lean_inc(x_168);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_168);
lean_ctor_set(x_646, 1, x_643);
x_647 = lean_array_get_size(x_645);
x_648 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0;
x_649 = lean_int_dec_lt(x_168, x_648);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; uint64_t x_653; 
x_650 = lean_nat_abs(x_168);
x_651 = lean_unsigned_to_nat(2u);
x_652 = lean_nat_mul(x_651, x_650);
lean_dec(x_650);
x_653 = lean_uint64_of_nat(x_652);
lean_dec(x_652);
x_345 = x_633;
x_346 = x_645;
x_347 = x_638;
x_348 = x_640;
x_349 = x_641;
x_350 = x_634;
x_351 = x_644;
x_352 = x_636;
x_353 = x_635;
x_354 = x_637;
x_355 = x_646;
x_356 = x_639;
x_357 = x_643;
x_358 = x_647;
x_359 = x_642;
x_360 = x_653;
goto block_632;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint64_t x_660; 
x_654 = lean_nat_abs(x_168);
x_655 = lean_unsigned_to_nat(1u);
x_656 = lean_nat_sub(x_654, x_655);
lean_dec(x_654);
x_657 = lean_unsigned_to_nat(2u);
x_658 = lean_nat_mul(x_657, x_656);
lean_dec(x_656);
x_659 = lean_nat_add(x_658, x_655);
lean_dec(x_658);
x_660 = lean_uint64_of_nat(x_659);
lean_dec(x_659);
x_345 = x_633;
x_346 = x_645;
x_347 = x_638;
x_348 = x_640;
x_349 = x_641;
x_350 = x_634;
x_351 = x_644;
x_352 = x_636;
x_353 = x_635;
x_354 = x_637;
x_355 = x_646;
x_356 = x_639;
x_357 = x_643;
x_358 = x_647;
x_359 = x_642;
x_360 = x_660;
goto block_632;
}
}
block_673:
{
lean_object* x_672; 
x_672 = lean_ctor_get(x_161, 0);
lean_inc(x_672);
x_633 = x_664;
x_634 = x_662;
x_635 = x_667;
x_636 = x_663;
x_637 = x_668;
x_638 = x_665;
x_639 = x_669;
x_640 = x_666;
x_641 = x_670;
x_642 = x_671;
x_643 = x_672;
goto block_661;
}
block_689:
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_680 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = l_Lean_MessageData_ofFormat(x_680);
x_682 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_682, 0, x_678);
lean_ctor_set(x_682, 1, x_681);
x_683 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_677);
x_684 = l_Lean_MessageData_ofExpr(x_674);
x_685 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_676);
x_687 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_163, x_686, x_9, x_10, x_11, x_12, x_675);
x_688 = lean_ctor_get(x_687, 1);
lean_inc(x_688);
lean_dec(x_687);
x_662 = x_4;
x_663 = x_5;
x_664 = x_6;
x_665 = x_7;
x_666 = x_8;
x_667 = x_9;
x_668 = x_10;
x_669 = x_11;
x_670 = x_12;
x_671 = x_688;
goto block_673;
}
}
else
{
uint8_t x_724; 
lean_dec(x_12);
lean_dec(x_11);
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
x_724 = !lean_is_exclusive(x_160);
if (x_724 == 0)
{
return x_160;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_160, 0);
x_726 = lean_ctor_get(x_160, 1);
lean_inc(x_726);
lean_inc(x_725);
lean_dec(x_160);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set(x_727, 1, x_726);
return x_727;
}
}
}
else
{
uint8_t x_728; 
lean_dec(x_12);
lean_dec(x_11);
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
x_728 = !lean_is_exclusive(x_156);
if (x_728 == 0)
{
return x_156;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_156, 0);
x_730 = lean_ctor_get(x_156, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_156);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
block_58:
{
uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_25 = l_Lean_Grind_CommRing_hashPoly____x40_Init_Grind_Ring_Poly___hyg_4375_(x_22);
lean_dec(x_22);
x_26 = lean_uint64_mix_hash(x_24, x_25);
x_27 = lean_uint64_shift_right(x_26, x_20);
x_28 = lean_uint64_xor(x_26, x_27);
x_29 = lean_uint64_shift_right(x_28, x_18);
x_30 = lean_uint64_xor(x_28, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_33 = lean_usize_sub(x_32, x_15);
x_34 = lean_usize_land(x_31, x_33);
x_35 = lean_array_uget(x_14, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(x_19, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_16, x_37);
lean_dec(x_16);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_array_uset(x_14, x_34, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_nat_mul(x_38, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = lean_array_get_size(x_40);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2___redArg(x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_23);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_40);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_23);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_box(0);
x_53 = lean_array_uset(x_14, x_34, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(x_19, x_21, x_35);
x_55 = lean_array_uset(x_53, x_34, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_16);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_23);
return x_57;
}
}
block_81:
{
lean_object* x_72; 
x_72 = l_Lean_Meta_Grind_Arith_CommRing_propagateEq(x_2, x_59, x_3, x_60, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
lean_ctor_set(x_72, 0, x_1);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 0);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
block_110:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lean_MessageData_ofFormat(x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_82);
x_105 = l_Lean_MessageData_ofExpr(x_98);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_83, x_107, x_87, x_89, x_94, x_96, x_84);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_59 = x_91;
x_60 = x_97;
x_61 = x_88;
x_62 = x_85;
x_63 = x_92;
x_64 = x_86;
x_65 = x_93;
x_66 = x_95;
x_67 = x_87;
x_68 = x_89;
x_69 = x_94;
x_70 = x_96;
x_71 = x_109;
goto block_81;
}
block_155:
{
uint64_t x_122; uint64_t x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; size_t x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; uint8_t x_133; 
x_122 = l_Lean_Grind_CommRing_hashPoly____x40_Init_Grind_Ring_Poly___hyg_4375_(x_120);
lean_dec(x_120);
x_123 = lean_uint64_mix_hash(x_121, x_122);
x_124 = lean_uint64_shift_right(x_123, x_117);
x_125 = lean_uint64_xor(x_123, x_124);
x_126 = lean_uint64_shift_right(x_125, x_115);
x_127 = lean_uint64_xor(x_125, x_126);
x_128 = lean_uint64_to_usize(x_127);
x_129 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_130 = lean_usize_sub(x_129, x_112);
x_131 = lean_usize_land(x_128, x_130);
x_132 = lean_array_uget(x_111, x_131);
x_133 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(x_119, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_113, x_134);
lean_dec(x_113);
x_136 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_136, 0, x_119);
lean_ctor_set(x_136, 1, x_114);
lean_ctor_set(x_136, 2, x_132);
x_137 = lean_array_uset(x_111, x_131, x_136);
x_138 = lean_unsigned_to_nat(4u);
x_139 = lean_nat_mul(x_135, x_138);
x_140 = lean_unsigned_to_nat(3u);
x_141 = lean_nat_div(x_139, x_140);
lean_dec(x_139);
x_142 = lean_array_get_size(x_137);
x_143 = lean_nat_dec_le(x_141, x_142);
lean_dec(x_142);
lean_dec(x_141);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__2___redArg(x_137);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_135);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_118);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_135);
lean_ctor_set(x_147, 1, x_137);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_118);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_box(0);
x_150 = lean_array_uset(x_111, x_131, x_149);
x_151 = l_Std_DHashMap_Internal_AssocList_replace___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__5___redArg(x_119, x_114, x_132);
x_152 = lean_array_uset(x_150, x_131, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_113);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_118);
return x_154;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_6, x_5);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = lean_array_uget(x_4, x_6);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_21);
lean_inc(x_1);
x_24 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(x_1, x_2, x_23, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_7, 0, x_28);
lean_ctor_set(x_24, 0, x_7);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_7, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_33);
lean_ctor_set(x_7, 0, x_3);
x_34 = 1;
x_35 = lean_usize_add(x_6, x_34);
x_6 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_free_object(x_7);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_7, 1);
lean_inc(x_41);
lean_dec(x_7);
x_42 = lean_array_uget(x_4, x_6);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_41);
lean_inc(x_1);
x_43 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(x_1, x_2, x_42, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; 
lean_dec(x_41);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
lean_inc(x_3);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_51);
x_53 = 1;
x_54 = lean_usize_add(x_6, x_53);
x_6 = x_54;
x_7 = x_52;
x_17 = x_50;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_41);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_56 = lean_ctor_get(x_43, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_43, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_58 = x_43;
} else {
 lean_dec_ref(x_43);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_23 = lean_apply_12(x_1, x_22, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_6, 0, x_27);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_6, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_20);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_32);
lean_ctor_set(x_6, 0, x_2);
x_33 = 1;
x_34 = lean_usize_add(x_5, x_33);
x_5 = x_34;
x_16 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_6);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_dec(x_6);
x_41 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_40);
x_42 = lean_apply_12(x_1, x_41, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
lean_dec(x_40);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
x_16 = x_49;
goto _start;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr.0.Lean.Meta.Grind.Arith.CommRing.propagateEqs", 100, 100);
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13;
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_unsigned_to_nat(367u);
x_4 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0;
x_5 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_5, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1;
x_25 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_3, 0, x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_3, 0, x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_19, x_2, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_39, 0, x_22);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_3, 1, x_42);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_22, 0, x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_22);
lean_free_object(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_19, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
lean_ctor_set(x_3, 1, x_51);
lean_ctor_set(x_3, 0, x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_3);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_3);
lean_dec(x_1);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
lean_dec(x_3);
lean_inc(x_2);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1;
x_69 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
lean_dec(x_1);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
lean_dec(x_65);
x_80 = lean_ctor_get(x_66, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_81 = x_66;
} else {
 lean_dec_ref(x_66);
 x_81 = lean_box(0);
}
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_64, x_2, x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_81);
lean_dec(x_1);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_64);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_65, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_65, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_95 = x_65;
} else {
 lean_dec_ref(x_65);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_14);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_14, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 0);
lean_dec(x_100);
x_101 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
lean_ctor_set(x_3, 0, x_101);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_14, 0, x_102);
return x_14;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_3, 1);
lean_inc(x_103);
lean_dec(x_3);
x_104 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_14, 0, x_106);
return x_14;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_14, 1);
lean_inc(x_107);
lean_dec(x_14);
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_109 = x_3;
} else {
 lean_dec_ref(x_3);
 x_109 = lean_box(0);
}
x_110 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_107);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_array_size(x_16);
x_20 = 0;
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0(x_1, x_2, x_17, x_16, x_19, x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_26);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_22);
lean_free_object(x_3);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_3);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_3, 0);
lean_inc(x_40);
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
x_43 = lean_array_size(x_40);
x_44 = 0;
x_45 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0(x_1, x_2, x_41, x_40, x_43, x_44, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_46);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_59 = x_45;
} else {
 lean_dec_ref(x_45);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0), 13, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
x_66 = lean_array_size(x_62);
x_67 = 0;
x_68 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1(x_63, x_64, x_62, x_66, x_67, x_65, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_68, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
lean_ctor_set(x_3, 0, x_73);
lean_ctor_set(x_68, 0, x_3);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
lean_ctor_set(x_3, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_3);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_69);
lean_free_object(x_3);
x_77 = !lean_is_exclusive(x_68);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_68, 0);
lean_dec(x_78);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_79);
return x_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
lean_dec(x_68);
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_free_object(x_3);
x_83 = !lean_is_exclusive(x_68);
if (x_83 == 0)
{
return x_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_68, 0);
x_85 = lean_ctor_get(x_68, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_68);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; size_t x_91; size_t x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
lean_dec(x_3);
x_88 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0), 13, 1);
lean_closure_set(x_88, 0, x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_4);
x_91 = lean_array_size(x_87);
x_92 = 0;
x_93 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1(x_88, x_89, x_87, x_91, x_92, x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_94);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_102 = x_93;
} else {
 lean_dec_ref(x_93);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_95, 0);
lean_inc(x_103);
lean_dec(x_95);
if (lean_is_scalar(x_102)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_102;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_107 = x_93;
} else {
 lean_dec_ref(x_93);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_5, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 0);
lean_dec(x_21);
x_22 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_23 = lean_apply_12(x_1, x_22, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_6, 0, x_29);
lean_ctor_set(x_23, 0, x_6);
return x_23;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_32;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_6, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
lean_dec(x_20);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_2);
x_37 = 1;
x_38 = lean_usize_add(x_5, x_37);
x_5 = x_38;
x_16 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_free_object(x_6);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_dec(x_6);
x_45 = lean_array_uget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_44);
x_46 = lean_apply_12(x_1, x_45, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; 
lean_dec(x_44);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ctor_get(x_47, 0);
lean_inc(x_56);
lean_dec(x_47);
lean_inc(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
x_58 = 1;
x_59 = lean_usize_add(x_5, x_58);
x_5 = x_59;
x_6 = x_57;
x_16 = x_55;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_44);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_63 = x_46;
} else {
 lean_dec_ref(x_46);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_5, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 0);
lean_dec(x_20);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1;
x_25 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_3, 0, x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
lean_ctor_set(x_3, 0, x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_dec(x_21);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_19, x_2, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set(x_3, 1, x_41);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_39, 0, x_22);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_3, 1, x_42);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_22, 0, x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_22);
lean_free_object(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
return x_39;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_22, 0);
lean_inc(x_49);
lean_dec(x_22);
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_19, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
lean_ctor_set(x_3, 1, x_51);
lean_ctor_set(x_3, 0, x_1);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_3);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_free_object(x_3);
lean_dec(x_1);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_58 = x_50;
} else {
 lean_dec_ref(x_50);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_3);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_21);
if (x_60 == 0)
{
return x_21;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_21, 0);
x_62 = lean_ctor_get(x_21, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_21);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
lean_dec(x_3);
lean_inc(x_2);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1;
x_69 = l_panic___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_64);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
lean_dec(x_1);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
lean_dec(x_65);
x_80 = lean_ctor_get(x_66, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_81 = x_66;
} else {
 lean_dec_ref(x_66);
 x_81 = lean_box(0);
}
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_64, x_2, x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_1);
lean_ctor_set(x_86, 1, x_83);
if (lean_is_scalar(x_81)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_81;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_81);
lean_dec(x_1);
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_64);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_65, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_65, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_95 = x_65;
} else {
 lean_dec_ref(x_65);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_14);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_14, 0);
lean_dec(x_98);
x_99 = !lean_is_exclusive(x_3);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_3, 0);
lean_dec(x_100);
x_101 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
lean_ctor_set(x_3, 0, x_101);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_3);
lean_ctor_set(x_14, 0, x_102);
return x_14;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_3, 1);
lean_inc(x_103);
lean_dec(x_3);
x_104 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_14, 0, x_106);
return x_14;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_14, 1);
lean_inc(x_107);
lean_dec(x_14);
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_109 = x_3;
} else {
 lean_dec_ref(x_3);
 x_109 = lean_box(0);
}
x_110 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_107);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(x_1, x_3, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0___lam__0), 13, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
x_29 = lean_array_size(x_15);
x_30 = 0;
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3(x_26, x_27, x_15, x_29, x_30, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
lean_dec(x_15);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_32);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_31, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_5, x_7, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_ctor_get(x_3, 0);
lean_dec(x_22);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_21, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
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
lean_ctor_set(x_3, 1, x_27);
lean_ctor_set(x_3, 0, x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_3);
lean_dec(x_1);
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
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
lean_dec(x_3);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process(x_35, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_45 = x_36;
} else {
 lean_dec_ref(x_36);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_16, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
lean_dec(x_50);
x_51 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
lean_ctor_set(x_3, 0, x_51);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_16, 0, x_52);
return x_16;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_dec(x_3);
x_54 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_16, 0, x_56);
return x_16;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_16, 1);
lean_inc(x_57);
lean_dec(x_16);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_59 = x_3;
} else {
 lean_dec_ref(x_3);
 x_59 = lean_box(0);
}
x_60 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2;
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Grind_isInconsistent___redArg(x_2, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 19);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0(x_19, x_18, x_20, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 21);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___lam__0), 13, 1);
lean_closure_set(x_32, 0, x_19);
lean_ctor_set(x_22, 0, x_19);
x_33 = l_Lean_PersistentHashMap_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(x_31, x_22, x_32, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_dec(x_33);
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
lean_dec(x_35);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_33, 0);
x_50 = lean_ctor_get(x_33, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_33);
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
lean_free_object(x_22);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_28);
if (x_52 == 0)
{
return x_28;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_28, 0);
x_54 = lean_ctor_get(x_28, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_28);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_dec(x_22);
x_57 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 21);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___lam__0), 13, 1);
lean_closure_set(x_61, 0, x_19);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_19);
lean_ctor_set(x_62, 1, x_56);
x_63 = l_Lean_PersistentHashMap_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(x_60, x_62, x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_65, 0);
lean_inc(x_72);
lean_dec(x_65);
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
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_63, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_76 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_ctor_get(x_57, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_80 = x_57;
} else {
 lean_dec_ref(x_57);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_21);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_21, 0);
lean_dec(x_83);
x_84 = lean_ctor_get(x_23, 0);
lean_inc(x_84);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_84);
return x_21;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_21, 1);
lean_inc(x_85);
lean_dec(x_21);
x_86 = lean_ctor_get(x_23, 0);
lean_inc(x_86);
lean_dec(x_23);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_21);
if (x_88 == 0)
{
return x_21;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_21, 0);
x_90 = lean_ctor_get(x_21, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_21);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_15);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_11);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_11, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_11, 0, x_98);
return x_11;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
lean_dec(x_11);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0___boxed(lean_object** _args) {
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
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__3(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_1);
x_16 = l_Lean_Core_checkSystem(x_1, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_26 = x_19;
} else {
 lean_dec_ref(x_19);
 x_26 = lean_box(0);
}
lean_inc(x_5);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_5, x_13, x_24);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_76;
goto block_72;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 1);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_25);
x_82 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_86 = l_Lean_MessageData_ofExpr(x_83);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_86);
lean_ctor_set(x_73, 0, x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_85);
lean_inc(x_5);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_5, x_87, x_11, x_12, x_13, x_14, x_84);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_89;
goto block_72;
}
else
{
uint8_t x_90; 
lean_free_object(x_73);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_73);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_80);
if (x_94 == 0)
{
return x_80;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_80, 0);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_80);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
lean_dec(x_73);
x_99 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_25);
x_101 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_105 = l_Lean_MessageData_ofExpr(x_102);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
lean_inc(x_5);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_5, x_107, x_11, x_12, x_13, x_14, x_103);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_109;
goto block_72;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_99, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_116 = x_99;
} else {
 lean_dec_ref(x_99);
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
block_72:
{
lean_object* x_37; 
lean_inc(x_30);
lean_inc(x_28);
x_37 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasis(x_25, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_isInconsistent___redArg(x_28, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_28, x_30, x_42);
lean_dec(x_30);
lean_dec(x_28);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_26);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_15 = x_46;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
x_50 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_26;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_26;
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_39);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
x_60 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_26;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_26;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_4);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_18);
if (x_118 == 0)
{
return x_18;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_18, 0);
x_120 = lean_ctor_get(x_18, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_18);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_16);
if (x_122 == 0)
{
return x_16;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_16, 0);
x_124 = lean_ctor_get(x_16, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_16);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_1);
x_16 = l_Lean_Core_checkSystem(x_1, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_26 = x_19;
} else {
 lean_dec_ref(x_19);
 x_26 = lean_box(0);
}
lean_inc(x_5);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_5, x_13, x_24);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_76;
goto block_72;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 1);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
lean_inc(x_25);
x_82 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_86 = l_Lean_MessageData_ofExpr(x_83);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_86);
lean_ctor_set(x_73, 0, x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_85);
lean_inc(x_5);
x_88 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_5, x_87, x_11, x_12, x_13, x_14, x_84);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_89;
goto block_72;
}
else
{
uint8_t x_90; 
lean_free_object(x_73);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
return x_82;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_82);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_free_object(x_73);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_80);
if (x_94 == 0)
{
return x_80;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_80, 0);
x_96 = lean_ctor_get(x_80, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_80);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_73, 1);
lean_inc(x_98);
lean_dec(x_73);
x_99 = l_Lean_Meta_Grind_updateLastTag(x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc(x_25);
x_101 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_denoteExpr___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__2(x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_105 = l_Lean_MessageData_ofExpr(x_102);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
lean_inc(x_5);
x_108 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_5, x_107, x_11, x_12, x_13, x_14, x_103);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_109;
goto block_72;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_99, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_116 = x_99;
} else {
 lean_dec_ref(x_99);
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
block_72:
{
lean_object* x_37; 
lean_inc(x_30);
lean_inc(x_28);
x_37 = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasis(x_25, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_isInconsistent___redArg(x_28, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_28, x_30, x_42);
lean_dec(x_30);
lean_dec(x_28);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_26);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
x_50 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_26;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_26;
}
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_39);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_39, 0);
lean_dec(x_59);
x_60 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_26;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
lean_ctor_set(x_39, 0, x_62);
return x_39;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_39, 1);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_box(x_3);
if (lean_is_scalar(x_26)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_26;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_4);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_37);
if (x_68 == 0)
{
return x_37;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_37, 0);
x_70 = lean_ctor_get(x_37, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_37);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_18);
if (x_118 == 0)
{
return x_18;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_18, 0);
x_120 = lean_ctor_get(x_18, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_18);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_16);
if (x_122 == 0)
{
return x_16;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_16, 0);
x_124 = lean_ctor_get(x_16, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_16);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; 
x_24 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
return x_24;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("check", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_3 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkRing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_needCheck(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_48; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_48 = lean_unbox(x_12);
if (x_48 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_50 = lean_ctor_get(x_11, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_11, 0);
lean_dec(x_51);
x_52 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_53 = l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1;
x_164 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_53, x_8, x_13);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_free_object(x_11);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_54 = x_1;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_167;
goto block_163;
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_164, 1);
x_170 = lean_ctor_get(x_164, 0);
lean_dec(x_170);
x_171 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_169);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_178 = l_Lean_MessageData_ofExpr(x_176);
lean_ctor_set_tag(x_164, 7);
lean_ctor_set(x_164, 1, x_178);
lean_ctor_set(x_164, 0, x_177);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_177);
lean_ctor_set(x_11, 0, x_164);
x_179 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_53, x_11, x_6, x_7, x_8, x_9, x_175);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_54 = x_1;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_180;
goto block_163;
}
else
{
uint8_t x_181; 
lean_free_object(x_164);
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_173);
if (x_181 == 0)
{
return x_173;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_173, 0);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_173);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_free_object(x_164);
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = !lean_is_exclusive(x_171);
if (x_185 == 0)
{
return x_171;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_171, 0);
x_187 = lean_ctor_get(x_171, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_171);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_164, 1);
lean_inc(x_189);
lean_dec(x_164);
x_190 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_197 = l_Lean_MessageData_ofExpr(x_195);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_196);
lean_ctor_set(x_11, 0, x_198);
x_199 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_53, x_11, x_6, x_7, x_8, x_9, x_194);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_54 = x_1;
x_55 = x_2;
x_56 = x_3;
x_57 = x_4;
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_200;
goto block_163;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_192, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_192, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_203 = x_192;
} else {
 lean_dec_ref(x_192);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_free_object(x_11);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_ctor_get(x_190, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_190, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_207 = x_190;
} else {
 lean_dec_ref(x_190);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
block_163:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_box(0);
x_65 = l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2;
x_66 = lean_unbox(x_12);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
x_67 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(x_52, x_65, x_66, x_64, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
lean_inc(x_55);
lean_inc(x_54);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs(x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_take(x_55, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 14);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_ctor_get(x_54, 0);
lean_inc(x_80);
lean_dec(x_54);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_76, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_76, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 4);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 5);
lean_inc(x_86);
x_87 = lean_ctor_get(x_76, 6);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 7);
lean_inc(x_88);
x_89 = lean_ctor_get_uint8(x_76, sizeof(void*)*16);
x_90 = lean_ctor_get(x_76, 8);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 9);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 10);
lean_inc(x_92);
x_93 = lean_ctor_get(x_76, 11);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 12);
lean_inc(x_94);
x_95 = lean_ctor_get(x_76, 13);
lean_inc(x_95);
x_96 = lean_ctor_get(x_76, 15);
lean_inc(x_96);
lean_dec(x_76);
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_77, 3);
lean_inc(x_99);
lean_dec(x_77);
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_78, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_78, 3);
lean_inc(x_103);
lean_dec(x_78);
x_104 = lean_array_get_size(x_100);
x_105 = lean_nat_dec_lt(x_80, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec(x_80);
x_14 = x_96;
x_15 = x_101;
x_16 = x_102;
x_17 = x_103;
x_18 = x_82;
x_19 = x_86;
x_20 = x_55;
x_21 = x_97;
x_22 = x_93;
x_23 = x_88;
x_24 = x_87;
x_25 = x_94;
x_26 = x_85;
x_27 = x_79;
x_28 = x_89;
x_29 = x_99;
x_30 = x_92;
x_31 = x_84;
x_32 = x_98;
x_33 = x_91;
x_34 = x_95;
x_35 = x_90;
x_36 = x_81;
x_37 = x_83;
x_38 = x_100;
goto block_47;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_array_fget(x_100, x_80);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_108 = lean_array_fset(x_100, x_80, x_64);
x_109 = lean_box(0);
x_110 = lean_unbox(x_109);
lean_ctor_set_uint8(x_106, sizeof(void*)*28, x_110);
x_111 = lean_array_fset(x_108, x_80, x_106);
lean_dec(x_80);
x_14 = x_96;
x_15 = x_101;
x_16 = x_102;
x_17 = x_103;
x_18 = x_82;
x_19 = x_86;
x_20 = x_55;
x_21 = x_97;
x_22 = x_93;
x_23 = x_88;
x_24 = x_87;
x_25 = x_94;
x_26 = x_85;
x_27 = x_79;
x_28 = x_89;
x_29 = x_99;
x_30 = x_92;
x_31 = x_84;
x_32 = x_98;
x_33 = x_91;
x_34 = x_95;
x_35 = x_90;
x_36 = x_81;
x_37 = x_83;
x_38 = x_111;
goto block_47;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_112 = lean_ctor_get(x_106, 0);
x_113 = lean_ctor_get(x_106, 1);
x_114 = lean_ctor_get(x_106, 2);
x_115 = lean_ctor_get(x_106, 3);
x_116 = lean_ctor_get(x_106, 4);
x_117 = lean_ctor_get(x_106, 5);
x_118 = lean_ctor_get(x_106, 6);
x_119 = lean_ctor_get(x_106, 7);
x_120 = lean_ctor_get(x_106, 8);
x_121 = lean_ctor_get(x_106, 9);
x_122 = lean_ctor_get(x_106, 10);
x_123 = lean_ctor_get(x_106, 11);
x_124 = lean_ctor_get(x_106, 12);
x_125 = lean_ctor_get(x_106, 13);
x_126 = lean_ctor_get(x_106, 14);
x_127 = lean_ctor_get(x_106, 15);
x_128 = lean_ctor_get(x_106, 16);
x_129 = lean_ctor_get(x_106, 17);
x_130 = lean_ctor_get(x_106, 18);
x_131 = lean_ctor_get(x_106, 19);
x_132 = lean_ctor_get(x_106, 20);
x_133 = lean_ctor_get(x_106, 21);
x_134 = lean_ctor_get(x_106, 22);
x_135 = lean_ctor_get(x_106, 23);
x_136 = lean_ctor_get(x_106, 24);
x_137 = lean_ctor_get(x_106, 25);
x_138 = lean_ctor_get(x_106, 26);
x_139 = lean_ctor_get(x_106, 27);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_106);
x_140 = lean_array_fset(x_100, x_80, x_64);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_142, 0, x_112);
lean_ctor_set(x_142, 1, x_113);
lean_ctor_set(x_142, 2, x_114);
lean_ctor_set(x_142, 3, x_115);
lean_ctor_set(x_142, 4, x_116);
lean_ctor_set(x_142, 5, x_117);
lean_ctor_set(x_142, 6, x_118);
lean_ctor_set(x_142, 7, x_119);
lean_ctor_set(x_142, 8, x_120);
lean_ctor_set(x_142, 9, x_121);
lean_ctor_set(x_142, 10, x_122);
lean_ctor_set(x_142, 11, x_123);
lean_ctor_set(x_142, 12, x_124);
lean_ctor_set(x_142, 13, x_125);
lean_ctor_set(x_142, 14, x_126);
lean_ctor_set(x_142, 15, x_127);
lean_ctor_set(x_142, 16, x_128);
lean_ctor_set(x_142, 17, x_129);
lean_ctor_set(x_142, 18, x_130);
lean_ctor_set(x_142, 19, x_131);
lean_ctor_set(x_142, 20, x_132);
lean_ctor_set(x_142, 21, x_133);
lean_ctor_set(x_142, 22, x_134);
lean_ctor_set(x_142, 23, x_135);
lean_ctor_set(x_142, 24, x_136);
lean_ctor_set(x_142, 25, x_137);
lean_ctor_set(x_142, 26, x_138);
lean_ctor_set(x_142, 27, x_139);
x_143 = lean_unbox(x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*28, x_143);
x_144 = lean_array_fset(x_140, x_80, x_142);
lean_dec(x_80);
x_14 = x_96;
x_15 = x_101;
x_16 = x_102;
x_17 = x_103;
x_18 = x_82;
x_19 = x_86;
x_20 = x_55;
x_21 = x_97;
x_22 = x_93;
x_23 = x_88;
x_24 = x_87;
x_25 = x_94;
x_26 = x_85;
x_27 = x_79;
x_28 = x_89;
x_29 = x_99;
x_30 = x_92;
x_31 = x_84;
x_32 = x_98;
x_33 = x_91;
x_34 = x_95;
x_35 = x_90;
x_36 = x_81;
x_37 = x_83;
x_38 = x_144;
goto block_47;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
x_145 = !lean_is_exclusive(x_73);
if (x_145 == 0)
{
return x_73;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_73, 0);
x_147 = lean_ctor_get(x_73, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_73);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
x_149 = !lean_is_exclusive(x_71);
if (x_149 == 0)
{
return x_71;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_71, 0);
x_151 = lean_ctor_get(x_71, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_71);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
x_153 = !lean_is_exclusive(x_67);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_67, 0);
lean_dec(x_154);
x_155 = lean_ctor_get(x_69, 0);
lean_inc(x_155);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_155);
return x_67;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_67, 1);
lean_inc(x_156);
lean_dec(x_67);
x_157 = lean_ctor_get(x_69, 0);
lean_inc(x_157);
lean_dec(x_69);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_12);
x_159 = !lean_is_exclusive(x_67);
if (x_159 == 0)
{
return x_67;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_67, 0);
x_161 = lean_ctor_get(x_67, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_67);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_dec(x_11);
x_209 = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1;
x_210 = l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1;
x_315 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__0___redArg(x_210, x_8, x_13);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_unbox(x_316);
lean_dec(x_316);
if (x_317 == 0)
{
lean_object* x_318; 
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
lean_dec(x_315);
x_211 = x_1;
x_212 = x_2;
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
x_217 = x_7;
x_218 = x_8;
x_219 = x_9;
x_220 = x_318;
goto block_314;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_320 = x_315;
} else {
 lean_dec_ref(x_315);
 x_320 = lean_box(0);
}
x_321 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_319);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
x_327 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3;
x_328 = l_Lean_MessageData_ofExpr(x_326);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(7, 2, 0);
} else {
 x_329 = x_320;
 lean_ctor_set_tag(x_329, 7);
}
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
x_331 = l_Lean_addTrace___at___Lean_Meta_Grind_Arith_CommRing_Null_setEqUnsat_spec__1___redArg(x_210, x_330, x_6, x_7, x_8, x_9, x_325);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_211 = x_1;
x_212 = x_2;
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
x_217 = x_7;
x_218 = x_8;
x_219 = x_9;
x_220 = x_332;
goto block_314;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_320);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_333 = lean_ctor_get(x_323, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_323, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_335 = x_323;
} else {
 lean_dec_ref(x_323);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_320);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_337 = lean_ctor_get(x_321, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_321, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_339 = x_321;
} else {
 lean_dec_ref(x_321);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
block_314:
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; 
x_221 = lean_box(0);
x_222 = l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2;
x_223 = lean_unbox(x_12);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_224 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(x_209, x_222, x_223, x_221, x_210, x_211, x_212, x_213, x_214, x_215, x_216, x_217, x_218, x_219, x_220);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(x_211, x_212, x_213, x_214, x_215, x_216, x_217, x_218, x_219, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
lean_inc(x_212);
lean_inc(x_211);
x_230 = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs(x_211, x_212, x_213, x_214, x_215, x_216, x_217, x_218, x_219, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_st_ref_take(x_212, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_233, 14);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_232, 1);
lean_inc(x_236);
lean_dec(x_232);
x_237 = lean_ctor_get(x_211, 0);
lean_inc(x_237);
lean_dec(x_211);
x_238 = lean_ctor_get(x_233, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_233, 1);
lean_inc(x_239);
x_240 = lean_ctor_get(x_233, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_233, 4);
lean_inc(x_242);
x_243 = lean_ctor_get(x_233, 5);
lean_inc(x_243);
x_244 = lean_ctor_get(x_233, 6);
lean_inc(x_244);
x_245 = lean_ctor_get(x_233, 7);
lean_inc(x_245);
x_246 = lean_ctor_get_uint8(x_233, sizeof(void*)*16);
x_247 = lean_ctor_get(x_233, 8);
lean_inc(x_247);
x_248 = lean_ctor_get(x_233, 9);
lean_inc(x_248);
x_249 = lean_ctor_get(x_233, 10);
lean_inc(x_249);
x_250 = lean_ctor_get(x_233, 11);
lean_inc(x_250);
x_251 = lean_ctor_get(x_233, 12);
lean_inc(x_251);
x_252 = lean_ctor_get(x_233, 13);
lean_inc(x_252);
x_253 = lean_ctor_get(x_233, 15);
lean_inc(x_253);
lean_dec(x_233);
x_254 = lean_ctor_get(x_234, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_234, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_234, 3);
lean_inc(x_256);
lean_dec(x_234);
x_257 = lean_ctor_get(x_235, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_235, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_235, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_235, 3);
lean_inc(x_260);
lean_dec(x_235);
x_261 = lean_array_get_size(x_257);
x_262 = lean_nat_dec_lt(x_237, x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_dec(x_237);
x_14 = x_253;
x_15 = x_258;
x_16 = x_259;
x_17 = x_260;
x_18 = x_239;
x_19 = x_243;
x_20 = x_212;
x_21 = x_254;
x_22 = x_250;
x_23 = x_245;
x_24 = x_244;
x_25 = x_251;
x_26 = x_242;
x_27 = x_236;
x_28 = x_246;
x_29 = x_256;
x_30 = x_249;
x_31 = x_241;
x_32 = x_255;
x_33 = x_248;
x_34 = x_252;
x_35 = x_247;
x_36 = x_238;
x_37 = x_240;
x_38 = x_257;
goto block_47;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; 
x_263 = lean_array_fget(x_257, x_237);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_263, 3);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 4);
lean_inc(x_268);
x_269 = lean_ctor_get(x_263, 5);
lean_inc(x_269);
x_270 = lean_ctor_get(x_263, 6);
lean_inc(x_270);
x_271 = lean_ctor_get(x_263, 7);
lean_inc(x_271);
x_272 = lean_ctor_get(x_263, 8);
lean_inc(x_272);
x_273 = lean_ctor_get(x_263, 9);
lean_inc(x_273);
x_274 = lean_ctor_get(x_263, 10);
lean_inc(x_274);
x_275 = lean_ctor_get(x_263, 11);
lean_inc(x_275);
x_276 = lean_ctor_get(x_263, 12);
lean_inc(x_276);
x_277 = lean_ctor_get(x_263, 13);
lean_inc(x_277);
x_278 = lean_ctor_get(x_263, 14);
lean_inc(x_278);
x_279 = lean_ctor_get(x_263, 15);
lean_inc(x_279);
x_280 = lean_ctor_get(x_263, 16);
lean_inc(x_280);
x_281 = lean_ctor_get(x_263, 17);
lean_inc(x_281);
x_282 = lean_ctor_get(x_263, 18);
lean_inc(x_282);
x_283 = lean_ctor_get(x_263, 19);
lean_inc(x_283);
x_284 = lean_ctor_get(x_263, 20);
lean_inc(x_284);
x_285 = lean_ctor_get(x_263, 21);
lean_inc(x_285);
x_286 = lean_ctor_get(x_263, 22);
lean_inc(x_286);
x_287 = lean_ctor_get(x_263, 23);
lean_inc(x_287);
x_288 = lean_ctor_get(x_263, 24);
lean_inc(x_288);
x_289 = lean_ctor_get(x_263, 25);
lean_inc(x_289);
x_290 = lean_ctor_get(x_263, 26);
lean_inc(x_290);
x_291 = lean_ctor_get(x_263, 27);
lean_inc(x_291);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 lean_ctor_release(x_263, 4);
 lean_ctor_release(x_263, 5);
 lean_ctor_release(x_263, 6);
 lean_ctor_release(x_263, 7);
 lean_ctor_release(x_263, 8);
 lean_ctor_release(x_263, 9);
 lean_ctor_release(x_263, 10);
 lean_ctor_release(x_263, 11);
 lean_ctor_release(x_263, 12);
 lean_ctor_release(x_263, 13);
 lean_ctor_release(x_263, 14);
 lean_ctor_release(x_263, 15);
 lean_ctor_release(x_263, 16);
 lean_ctor_release(x_263, 17);
 lean_ctor_release(x_263, 18);
 lean_ctor_release(x_263, 19);
 lean_ctor_release(x_263, 20);
 lean_ctor_release(x_263, 21);
 lean_ctor_release(x_263, 22);
 lean_ctor_release(x_263, 23);
 lean_ctor_release(x_263, 24);
 lean_ctor_release(x_263, 25);
 lean_ctor_release(x_263, 26);
 lean_ctor_release(x_263, 27);
 x_292 = x_263;
} else {
 lean_dec_ref(x_263);
 x_292 = lean_box(0);
}
x_293 = lean_array_fset(x_257, x_237, x_221);
x_294 = lean_box(0);
if (lean_is_scalar(x_292)) {
 x_295 = lean_alloc_ctor(0, 28, 1);
} else {
 x_295 = x_292;
}
lean_ctor_set(x_295, 0, x_264);
lean_ctor_set(x_295, 1, x_265);
lean_ctor_set(x_295, 2, x_266);
lean_ctor_set(x_295, 3, x_267);
lean_ctor_set(x_295, 4, x_268);
lean_ctor_set(x_295, 5, x_269);
lean_ctor_set(x_295, 6, x_270);
lean_ctor_set(x_295, 7, x_271);
lean_ctor_set(x_295, 8, x_272);
lean_ctor_set(x_295, 9, x_273);
lean_ctor_set(x_295, 10, x_274);
lean_ctor_set(x_295, 11, x_275);
lean_ctor_set(x_295, 12, x_276);
lean_ctor_set(x_295, 13, x_277);
lean_ctor_set(x_295, 14, x_278);
lean_ctor_set(x_295, 15, x_279);
lean_ctor_set(x_295, 16, x_280);
lean_ctor_set(x_295, 17, x_281);
lean_ctor_set(x_295, 18, x_282);
lean_ctor_set(x_295, 19, x_283);
lean_ctor_set(x_295, 20, x_284);
lean_ctor_set(x_295, 21, x_285);
lean_ctor_set(x_295, 22, x_286);
lean_ctor_set(x_295, 23, x_287);
lean_ctor_set(x_295, 24, x_288);
lean_ctor_set(x_295, 25, x_289);
lean_ctor_set(x_295, 26, x_290);
lean_ctor_set(x_295, 27, x_291);
x_296 = lean_unbox(x_294);
lean_ctor_set_uint8(x_295, sizeof(void*)*28, x_296);
x_297 = lean_array_fset(x_293, x_237, x_295);
lean_dec(x_237);
x_14 = x_253;
x_15 = x_258;
x_16 = x_259;
x_17 = x_260;
x_18 = x_239;
x_19 = x_243;
x_20 = x_212;
x_21 = x_254;
x_22 = x_250;
x_23 = x_245;
x_24 = x_244;
x_25 = x_251;
x_26 = x_242;
x_27 = x_236;
x_28 = x_246;
x_29 = x_256;
x_30 = x_249;
x_31 = x_241;
x_32 = x_255;
x_33 = x_248;
x_34 = x_252;
x_35 = x_247;
x_36 = x_238;
x_37 = x_240;
x_38 = x_297;
goto block_47;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_12);
x_298 = lean_ctor_get(x_230, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_230, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_300 = x_230;
} else {
 lean_dec_ref(x_230);
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
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_12);
x_302 = lean_ctor_get(x_228, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_228, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_304 = x_228;
} else {
 lean_dec_ref(x_228);
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
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_12);
x_306 = lean_ctor_get(x_224, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_307 = x_224;
} else {
 lean_dec_ref(x_224);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_226, 0);
lean_inc(x_308);
lean_dec(x_226);
if (lean_is_scalar(x_307)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_307;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_306);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_12);
x_310 = lean_ctor_get(x_224, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_224, 1);
lean_inc(x_311);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_312 = x_224;
} else {
 lean_dec_ref(x_224);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
}
block_47:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_15);
lean_ctor_set(x_39, 2, x_16);
lean_ctor_set(x_39, 3, x_17);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_29);
x_41 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_18);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_26);
lean_ctor_set(x_41, 5, x_19);
lean_ctor_set(x_41, 6, x_24);
lean_ctor_set(x_41, 7, x_23);
lean_ctor_set(x_41, 8, x_35);
lean_ctor_set(x_41, 9, x_33);
lean_ctor_set(x_41, 10, x_30);
lean_ctor_set(x_41, 11, x_22);
lean_ctor_set(x_41, 12, x_25);
lean_ctor_set(x_41, 13, x_34);
lean_ctor_set(x_41, 14, x_40);
lean_ctor_set(x_41, 15, x_14);
lean_ctor_set_uint8(x_41, sizeof(void*)*16, x_28);
x_42 = lean_st_ref_set(x_20, x_41, x_27);
lean_dec(x_20);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_12);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_12);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0_spec__0(x_1, x_2, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___redArg(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; lean_object* x_25; 
x_24 = lean_unbox(x_3);
lean_dec(x_3);
x_25 = l_Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_checkRing_spec__0(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_nat_dec_lt(x_5, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_5);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_checkRing(x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_43; uint8_t x_44; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_dec(x_4);
x_44 = lean_unbox(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_43);
x_45 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = x_45;
goto block_42;
}
else
{
uint8_t x_46; 
lean_dec(x_21);
x_46 = lean_unbox(x_43);
lean_dec(x_43);
x_23 = x_46;
goto block_42;
}
block_42:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Meta_Grind_isInconsistent___redArg(x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(x_23);
lean_inc(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_4 = x_29;
x_5 = x_30;
x_14 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_25);
x_35 = lean_box(x_23);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_25);
x_39 = lean_box(x_23);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_20);
if (x_47 == 0)
{
return x_20;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
x_49 = lean_ctor_get(x_20, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_20);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(x_1, x_3, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(x_1, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
lean_dec(x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_box(0);
lean_inc(x_25);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 0, x_39);
x_40 = lean_unbox(x_25);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(x_40, x_39, x_38, x_30, x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_42, 1);
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
lean_inc(x_46);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_46);
x_10 = x_42;
x_11 = x_44;
goto block_23;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
lean_inc(x_48);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_48);
x_10 = x_49;
x_11 = x_44;
goto block_23;
}
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_42, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
lean_dec(x_43);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_53);
x_10 = x_42;
x_11 = x_50;
goto block_23;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_dec(x_42);
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_10 = x_56;
x_11 = x_50;
goto block_23;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_41, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set_tag(x_59, 1);
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_57);
x_64 = !lean_is_exclusive(x_59);
if (x_64 == 0)
{
return x_59;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_59, 0);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_59);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_30, 0);
x_69 = lean_ctor_get(x_30, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_30);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_array_get_size(x_70);
lean_dec(x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_box(0);
lean_inc(x_25);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_25);
x_77 = lean_unbox(x_25);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_78 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(x_77, x_75, x_74, x_76, x_71, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_69);
lean_dec(x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
lean_inc(x_82);
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_82);
x_10 = x_84;
x_11 = x_81;
goto block_23;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
lean_dec(x_78);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_87 = x_79;
} else {
 lean_dec_ref(x_79);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
lean_dec(x_80);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_87;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
x_10 = x_89;
x_11 = x_85;
goto block_23;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_78, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_78, 1);
lean_inc(x_91);
lean_dec(x_78);
x_92 = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_90);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_98 = x_92;
} else {
 lean_dec_ref(x_92);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_28);
if (x_100 == 0)
{
return x_28;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_28, 0);
x_102 = lean_ctor_get(x_28, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_28);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_24);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_24, 0);
lean_dec(x_105);
x_106 = lean_box(0);
lean_ctor_set(x_24, 0, x_106);
return x_24;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_24, 1);
lean_inc(x_107);
lean_dec(x_24);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
block_23:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
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
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_check_spec__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_3);
return x_18;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_toRingExpr_x3f___closed__3);
l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0 = _init_l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0();
lean_mark_persistent(l_Lean_Grind_CommRing_Mon_findSimp_x3f___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2 = _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__2);
l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3 = _init_l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplifyWith___closed__3);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__0);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__1);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__2);
l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3 = _init_l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at___Lean_Loop_forIn_loop___at___Lean_Meta_Grind_Arith_CommRing_PolyDerivation_simplify_spec__0_spec__0___closed__3);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__2);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__3);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__4);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_checkConstant___closed__5);
l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_addToBasisCore___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToQueue___closed__1);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__0);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__1);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__2);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__3);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__4);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__5);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__6);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_Grind_Arith_CommRing_EqCnstr_superposeWith_spec__0_spec__0___redArg___closed__7);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_toMonic___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__2);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis_go___closed__3);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_simplifyBasis___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_addToBasisAfterSimp___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_saveDiseq___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_processNewEqImpl___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__11);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__12);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__13);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqToEq___closed__14);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_diseqZeroToEq___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_process___closed__11);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__0);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__1);
l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2 = _init_l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2();
lean_mark_persistent(l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at_____private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs_spec__0_spec__0___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr_0__Lean_Meta_Grind_Arith_CommRing_propagateEqs___closed__5);
l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__1);
l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2 = _init_l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_checkRing___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
