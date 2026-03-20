// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Order.Assert
// Imports: public import Lean.Meta.Tactic.Grind.Order.OrderM import Init.Grind.Propagator import Init.Grind.Order import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Order.Util import Lean.Meta.Tactic.Grind.Order.Proof
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_AssocList_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isLinearPreorder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_hasLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLeLinearPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "order"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "propagate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 44, 102, 149, 148, 89, 41, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "eq_trans_true"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 15, 222, 194, 99, 23, 253, 188)}};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Tactic.Grind.Order.Assert"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Grind.Order.propagateSelfEqTrue"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: c.u == c.v\n  "};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_trans_false"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 213, 247, 44, 34, 57, 174, 253)}};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Grind.Order.propagateSelfEqFalse"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "nat_eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 240, 39, 1, 35, 212, 161, 83)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "check_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 223, 60, 213, 11, 195, 227, 109)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "-ε"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "check_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 206, 15, 111, 12, 66, 29, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_addEdge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "add_edge"};
static const lean_object* l_Lean_Meta_Grind_Order_addEdge___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_addEdge___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 172, 169, 19, 106, 199, 68, 136)}};
static const lean_object* l_Lean_Meta_Grind_Order_addEdge___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_addEdge___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "eq_mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 160, 125, 46, 156, 174, 144, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(118, 196, 12, 238, 101, 107, 106, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "int_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 110, 8, 88, 103, 54, 255, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_not_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value),LEAN_SCALAR_PTR_LITERAL(68, 55, 231, 12, 192, 19, 143, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_not_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value),LEAN_SCALAR_PTR_LITERAL(22, 234, 13, 233, 13, 1, 104, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lt_of_not_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value),LEAN_SCALAR_PTR_LITERAL(12, 166, 193, 80, 9, 231, 149, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "le_of_not_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value),LEAN_SCALAR_PTR_LITERAL(106, 102, 104, 31, 59, 68, 161, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_not_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 116, 151, 104, 206, 219, 96, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_mp_not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value),LEAN_SCALAR_PTR_LITERAL(251, 101, 191, 216, 104, 179, 193, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "¬ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "eq_trans_false'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 158, 115, 194, 144, 122, 19, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_trans_true'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(38, 24, 59, 247, 190, 28, 198, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_of_eq_1"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 70, 170, 29, 105, 211, 134, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "le_of_eq_2"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(99, 146, 15, 83, 168, 123, 84, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_eq_1_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 93, 209, 5, 159, 56, 200, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_eq_2_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(82, 95, 72, 171, 241, 190, 67, 40)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_processNewEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_nat_eq"};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 179, 250, 96, 74, 22, 134, 180)}};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_processNewEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(lean_object* v_u_1_, lean_object* v_v_2_, lean_object* v_p_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_w_16_; lean_object* v_proof_17_; uint8_t v___x_18_; 
v_w_16_ = lean_ctor_get(v_p_3_, 0);
v_proof_17_ = lean_ctor_get(v_p_3_, 2);
v___x_18_ = lean_nat_dec_eq(v_u_1_, v_w_16_);
if (v___x_18_ == 0)
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Meta_Grind_Order_getProof(v_u_1_, v_w_16_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v___x_19_);
v___x_21_ = l_Lean_Meta_Grind_Order_mkTrans(v_a_20_, v_p_3_, v_v_2_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v___x_21_);
v_p_3_ = v_a_22_;
goto _start;
}
else
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_31_; 
v_a_24_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_31_ == 0)
{
v___x_26_ = v___x_21_;
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_21_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_31_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_29_; 
if (v_isShared_27_ == 0)
{
v___x_29_ = v___x_26_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_24_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
else
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
lean_dec_ref(v_p_3_);
v_a_32_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_19_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_19_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_object* v___x_40_; 
lean_inc_ref(v_proof_17_);
lean_dec_ref(v_p_3_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v_proof_17_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go___boxed(lean_object* v_u_41_, lean_object* v_v_42_, lean_object* v_p_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(v_u_41_, v_v_42_, v_p_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec(v_a_45_);
lean_dec(v_a_44_);
lean_dec(v_v_42_);
lean_dec(v_u_41_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(lean_object* v_u_57_, lean_object* v_v_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_Order_getProof(v_u_57_, v_v_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref(v___x_71_);
v___x_73_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(v_u_57_, v_v_58_, v_a_72_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
return v___x_73_;
}
else
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_81_; 
v_a_74_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_81_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_81_ == 0)
{
v___x_76_ = v___x_71_;
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_81_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_79_; 
if (v_isShared_77_ == 0)
{
v___x_79_ = v___x_76_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_a_74_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath___boxed(lean_object* v_u_82_, lean_object* v_v_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_82_, v_v_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec(v_a_85_);
lean_dec(v_a_84_);
lean_dec(v_v_83_);
lean_dec(v_u_82_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(lean_object* v_u_97_, lean_object* v_v_98_, lean_object* v_kuv_99_, lean_object* v_huv_100_, lean_object* v_kvu_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_98_, v_u_97_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_116_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref(v___x_114_);
v___x_116_ = l_Lean_Meta_Grind_Order_getExpr(v_u_97_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref(v___x_116_);
v___x_118_ = l_Lean_Meta_Grind_Order_getExpr(v_v_98_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref(v___x_118_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc(v_a_106_);
lean_inc_ref(v_a_105_);
lean_inc(v_a_104_);
lean_inc(v_a_103_);
v___x_120_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_a_117_, v_a_119_, v_kuv_99_, v_huv_100_, v_kvu_101_, v_a_115_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
v___x_122_ = l_Lean_Meta_Grind_closeGoal(v_a_121_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
return v___x_122_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
v_a_123_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_120_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_120_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec(v_a_117_);
lean_dec(v_a_115_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_huv_100_);
v_a_131_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_118_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_118_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec(v_a_115_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_huv_100_);
v_a_139_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_116_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_116_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
lean_dec_ref(v_a_105_);
lean_dec(v_a_104_);
lean_dec(v_a_103_);
lean_dec(v_a_102_);
lean_dec_ref(v_huv_100_);
v_a_147_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_114_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_114_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat___boxed(lean_object** _args){
lean_object* v_u_155_ = _args[0];
lean_object* v_v_156_ = _args[1];
lean_object* v_kuv_157_ = _args[2];
lean_object* v_huv_158_ = _args[3];
lean_object* v_kvu_159_ = _args[4];
lean_object* v_a_160_ = _args[5];
lean_object* v_a_161_ = _args[6];
lean_object* v_a_162_ = _args[7];
lean_object* v_a_163_ = _args[8];
lean_object* v_a_164_ = _args[9];
lean_object* v_a_165_ = _args[10];
lean_object* v_a_166_ = _args[11];
lean_object* v_a_167_ = _args[12];
lean_object* v_a_168_ = _args[13];
lean_object* v_a_169_ = _args[14];
lean_object* v_a_170_ = _args[15];
lean_object* v_a_171_ = _args[16];
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_155_, v_v_156_, v_kuv_157_, v_huv_158_, v_kvu_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec_ref(v_kvu_159_);
lean_dec_ref(v_kuv_157_);
lean_dec(v_v_156_);
lean_dec(v_u_155_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
else
{
lean_object* v_key_176_; lean_object* v_tail_177_; uint8_t v___x_178_; 
v_key_176_ = lean_ctor_get(v_x_174_, 0);
v_tail_177_ = lean_ctor_get(v_x_174_, 2);
v___x_178_ = lean_nat_dec_eq(v_key_176_, v_a_173_);
if (v___x_178_ == 0)
{
v_x_174_ = v_tail_177_;
goto _start;
}
else
{
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg___boxed(lean_object* v_a_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_180_, v_x_181_);
lean_dec(v_x_181_);
lean_dec(v_a_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(lean_object* v_a_184_, lean_object* v_b_185_, lean_object* v_x_186_){
_start:
{
if (lean_obj_tag(v_x_186_) == 0)
{
lean_dec(v_b_185_);
lean_dec(v_a_184_);
return v_x_186_;
}
else
{
lean_object* v_key_187_; lean_object* v_value_188_; lean_object* v_tail_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_201_; 
v_key_187_ = lean_ctor_get(v_x_186_, 0);
v_value_188_ = lean_ctor_get(v_x_186_, 1);
v_tail_189_ = lean_ctor_get(v_x_186_, 2);
v_isSharedCheck_201_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_201_ == 0)
{
v___x_191_ = v_x_186_;
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_tail_189_);
lean_inc(v_value_188_);
lean_inc(v_key_187_);
lean_dec(v_x_186_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_eq(v_key_187_, v_a_184_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_184_, v_b_185_, v_tail_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 2, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_key_187_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v_value_188_);
lean_ctor_set(v_reuseFailAlloc_197_, 2, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_value_188_);
lean_dec(v_key_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v_b_185_);
lean_ctor_set(v___x_191_, 0, v_a_184_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_184_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_b_185_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_tail_189_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(lean_object* v_m_202_, lean_object* v_k_203_, lean_object* v_v_204_){
_start:
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_k_203_, v_m_202_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_206_, 0, v_k_203_);
lean_ctor_set(v___x_206_, 1, v_v_204_);
lean_ctor_set(v___x_206_, 2, v_m_202_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_k_203_, v_v_204_, v_m_202_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(lean_object* v_u_208_, lean_object* v_k_209_, lean_object* v_x_210_, size_t v_x_211_, size_t v_x_212_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v_cs_213_; size_t v_j_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
v_cs_213_ = lean_ctor_get(v_x_210_, 0);
v_j_214_ = lean_usize_shift_right(v_x_211_, v_x_212_);
v___x_215_ = lean_usize_to_nat(v_j_214_);
v___x_216_ = lean_array_get_size(v_cs_213_);
v___x_217_ = lean_nat_dec_lt(v___x_215_, v___x_216_);
if (v___x_217_ == 0)
{
lean_dec(v___x_215_);
lean_dec_ref(v_k_209_);
lean_dec(v_u_208_);
return v_x_210_;
}
else
{
lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_235_; 
lean_inc_ref(v_cs_213_);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v_x_210_, 0);
lean_dec(v_unused_236_);
v___x_219_ = v_x_210_;
v_isShared_220_ = v_isSharedCheck_235_;
goto v_resetjp_218_;
}
else
{
lean_dec(v_x_210_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_235_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; size_t v_i_224_; size_t v___x_225_; size_t v_shift_226_; lean_object* v_v_227_; lean_object* v___x_228_; lean_object* v_xs_x27_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_221_ = ((size_t)1ULL);
v___x_222_ = lean_usize_shift_left(v___x_221_, v_x_212_);
v___x_223_ = lean_usize_sub(v___x_222_, v___x_221_);
v_i_224_ = lean_usize_land(v_x_211_, v___x_223_);
v___x_225_ = ((size_t)5ULL);
v_shift_226_ = lean_usize_sub(v_x_212_, v___x_225_);
v_v_227_ = lean_array_fget(v_cs_213_, v___x_215_);
v___x_228_ = lean_box(0);
v_xs_x27_229_ = lean_array_fset(v_cs_213_, v___x_215_, v___x_228_);
v___x_230_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(v_u_208_, v_k_209_, v_v_227_, v_i_224_, v_shift_226_);
v___x_231_ = lean_array_fset(v_xs_x27_229_, v___x_215_, v___x_230_);
lean_dec(v___x_215_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_231_);
v___x_233_ = v___x_219_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_vs_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_vs_237_ = lean_ctor_get(v_x_210_, 0);
v___x_238_ = lean_usize_to_nat(v_x_211_);
v___x_239_ = lean_array_get_size(v_vs_237_);
v___x_240_ = lean_nat_dec_lt(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v___x_238_);
lean_dec_ref(v_k_209_);
lean_dec(v_u_208_);
return v_x_210_;
}
else
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_252_; 
lean_inc_ref(v_vs_237_);
v_isSharedCheck_252_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v_x_210_, 0);
lean_dec(v_unused_253_);
v___x_242_ = v_x_210_;
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_x_210_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_252_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_v_244_; lean_object* v___x_245_; lean_object* v_xs_x27_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v_v_244_ = lean_array_fget(v_vs_237_, v___x_238_);
v___x_245_ = lean_box(0);
v_xs_x27_246_ = lean_array_fset(v_vs_237_, v___x_238_, v___x_245_);
v___x_247_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_244_, v_u_208_, v_k_209_);
v___x_248_ = lean_array_fset(v_xs_x27_246_, v___x_238_, v___x_247_);
lean_dec(v___x_238_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_248_);
v___x_250_ = v___x_242_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg___boxed(lean_object* v_u_254_, lean_object* v_k_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
size_t v_x_308__boxed_259_; size_t v_x_309__boxed_260_; lean_object* v_res_261_; 
v_x_308__boxed_259_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_309__boxed_260_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_261_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(v_u_254_, v_k_255_, v_x_256_, v_x_308__boxed_259_, v_x_309__boxed_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object* v_u_262_, lean_object* v_k_263_, lean_object* v_inst_264_, lean_object* v_t_265_, lean_object* v_i_266_){
_start:
{
lean_object* v_root_267_; lean_object* v_tail_268_; lean_object* v_size_269_; size_t v_shift_270_; lean_object* v_tailOff_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_295_; 
v_root_267_ = lean_ctor_get(v_t_265_, 0);
v_tail_268_ = lean_ctor_get(v_t_265_, 1);
v_size_269_ = lean_ctor_get(v_t_265_, 2);
v_shift_270_ = lean_ctor_get_usize(v_t_265_, 4);
v_tailOff_271_ = lean_ctor_get(v_t_265_, 3);
v_isSharedCheck_295_ = !lean_is_exclusive(v_t_265_);
if (v_isSharedCheck_295_ == 0)
{
v___x_273_ = v_t_265_;
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_tailOff_271_);
lean_inc(v_size_269_);
lean_inc(v_tail_268_);
lean_inc(v_root_267_);
lean_dec(v_t_265_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_295_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_nat_dec_le(v_tailOff_271_, v_i_266_);
if (v___x_275_ == 0)
{
size_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_usize_of_nat(v_i_266_);
v___x_277_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(v_u_262_, v_k_263_, v_root_267_, v___x_276_, v_shift_270_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_277_);
v___x_279_ = v___x_273_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_tail_268_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_size_269_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_tailOff_271_);
lean_ctor_set_usize(v_reuseFailAlloc_280_, 4, v_shift_270_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = lean_nat_sub(v_i_266_, v_tailOff_271_);
v___x_282_ = lean_array_get_size(v_tail_268_);
v___x_283_ = lean_nat_dec_lt(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_285_; 
lean_dec(v___x_281_);
lean_dec_ref(v_k_263_);
lean_dec(v_u_262_);
if (v_isShared_274_ == 0)
{
v___x_285_ = v___x_273_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_root_267_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_tail_268_);
lean_ctor_set(v_reuseFailAlloc_286_, 2, v_size_269_);
lean_ctor_set(v_reuseFailAlloc_286_, 3, v_tailOff_271_);
lean_ctor_set_usize(v_reuseFailAlloc_286_, 4, v_shift_270_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
lean_object* v_v_287_; lean_object* v___x_288_; lean_object* v_xs_x27_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v_v_287_ = lean_array_fget(v_tail_268_, v___x_281_);
v___x_288_ = lean_box(0);
v_xs_x27_289_ = lean_array_fset(v_tail_268_, v___x_281_, v___x_288_);
v___x_290_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_287_, v_u_262_, v_k_263_);
v___x_291_ = lean_array_fset(v_xs_x27_289_, v___x_281_, v___x_290_);
lean_dec(v___x_281_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 1, v___x_291_);
v___x_293_ = v___x_273_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_root_267_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_size_269_);
lean_ctor_set(v_reuseFailAlloc_294_, 3, v_tailOff_271_);
lean_ctor_set_usize(v_reuseFailAlloc_294_, 4, v_shift_270_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object* v_u_296_, lean_object* v_k_297_, lean_object* v_inst_298_, lean_object* v_t_299_, lean_object* v_i_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_296_, v_k_297_, v_inst_298_, v_t_299_, v_i_300_);
lean_dec(v_i_300_);
lean_dec(v_inst_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object* v_u_302_, lean_object* v_k_303_, lean_object* v___x_304_, lean_object* v_v_305_, lean_object* v_s_306_){
_start:
{
lean_object* v_id_307_; lean_object* v_type_308_; lean_object* v_u_309_; lean_object* v_isPreorderInst_310_; lean_object* v_leInst_311_; lean_object* v_ltInst_x3f_312_; lean_object* v_isPartialInst_x3f_313_; lean_object* v_isLinearPreInst_x3f_314_; lean_object* v_lawfulOrderLTInst_x3f_315_; lean_object* v_ringId_x3f_316_; uint8_t v_isCommRing_317_; lean_object* v_ringInst_x3f_318_; lean_object* v_orderedRingInst_x3f_319_; lean_object* v_leFn_320_; lean_object* v_ltFn_x3f_321_; lean_object* v_nodes_322_; lean_object* v_nodeMap_323_; lean_object* v_cnstrs_324_; lean_object* v_cnstrsOf_325_; lean_object* v_sources_326_; lean_object* v_targets_327_; lean_object* v_proofs_328_; lean_object* v_propagate_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_338_; 
v_id_307_ = lean_ctor_get(v_s_306_, 0);
v_type_308_ = lean_ctor_get(v_s_306_, 1);
v_u_309_ = lean_ctor_get(v_s_306_, 2);
v_isPreorderInst_310_ = lean_ctor_get(v_s_306_, 3);
v_leInst_311_ = lean_ctor_get(v_s_306_, 4);
v_ltInst_x3f_312_ = lean_ctor_get(v_s_306_, 5);
v_isPartialInst_x3f_313_ = lean_ctor_get(v_s_306_, 6);
v_isLinearPreInst_x3f_314_ = lean_ctor_get(v_s_306_, 7);
v_lawfulOrderLTInst_x3f_315_ = lean_ctor_get(v_s_306_, 8);
v_ringId_x3f_316_ = lean_ctor_get(v_s_306_, 9);
v_isCommRing_317_ = lean_ctor_get_uint8(v_s_306_, sizeof(void*)*22);
v_ringInst_x3f_318_ = lean_ctor_get(v_s_306_, 10);
v_orderedRingInst_x3f_319_ = lean_ctor_get(v_s_306_, 11);
v_leFn_320_ = lean_ctor_get(v_s_306_, 12);
v_ltFn_x3f_321_ = lean_ctor_get(v_s_306_, 13);
v_nodes_322_ = lean_ctor_get(v_s_306_, 14);
v_nodeMap_323_ = lean_ctor_get(v_s_306_, 15);
v_cnstrs_324_ = lean_ctor_get(v_s_306_, 16);
v_cnstrsOf_325_ = lean_ctor_get(v_s_306_, 17);
v_sources_326_ = lean_ctor_get(v_s_306_, 18);
v_targets_327_ = lean_ctor_get(v_s_306_, 19);
v_proofs_328_ = lean_ctor_get(v_s_306_, 20);
v_propagate_329_ = lean_ctor_get(v_s_306_, 21);
v_isSharedCheck_338_ = !lean_is_exclusive(v_s_306_);
if (v_isSharedCheck_338_ == 0)
{
v___x_331_ = v_s_306_;
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_propagate_329_);
lean_inc(v_proofs_328_);
lean_inc(v_targets_327_);
lean_inc(v_sources_326_);
lean_inc(v_cnstrsOf_325_);
lean_inc(v_cnstrs_324_);
lean_inc(v_nodeMap_323_);
lean_inc(v_nodes_322_);
lean_inc(v_ltFn_x3f_321_);
lean_inc(v_leFn_320_);
lean_inc(v_orderedRingInst_x3f_319_);
lean_inc(v_ringInst_x3f_318_);
lean_inc(v_ringId_x3f_316_);
lean_inc(v_lawfulOrderLTInst_x3f_315_);
lean_inc(v_isLinearPreInst_x3f_314_);
lean_inc(v_isPartialInst_x3f_313_);
lean_inc(v_ltInst_x3f_312_);
lean_inc(v_leInst_311_);
lean_inc(v_isPreorderInst_310_);
lean_inc(v_u_309_);
lean_inc(v_type_308_);
lean_inc(v_id_307_);
lean_dec(v_s_306_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_338_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
lean_inc_ref(v_k_303_);
lean_inc(v_u_302_);
v___x_333_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_302_, v_k_303_, v___x_304_, v_sources_326_, v_v_305_);
v___x_334_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_v_305_, v_k_303_, v___x_304_, v_targets_327_, v_u_302_);
lean_dec(v_u_302_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 19, v___x_334_);
lean_ctor_set(v___x_331_, 18, v___x_333_);
v___x_336_ = v___x_331_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_id_307_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_type_308_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_u_309_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_isPreorderInst_310_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_leInst_311_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v_ltInst_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_isPartialInst_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v_isLinearPreInst_x3f_314_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_lawfulOrderLTInst_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_337_, 9, v_ringId_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 10, v_ringInst_x3f_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 11, v_orderedRingInst_x3f_319_);
lean_ctor_set(v_reuseFailAlloc_337_, 12, v_leFn_320_);
lean_ctor_set(v_reuseFailAlloc_337_, 13, v_ltFn_x3f_321_);
lean_ctor_set(v_reuseFailAlloc_337_, 14, v_nodes_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 15, v_nodeMap_323_);
lean_ctor_set(v_reuseFailAlloc_337_, 16, v_cnstrs_324_);
lean_ctor_set(v_reuseFailAlloc_337_, 17, v_cnstrsOf_325_);
lean_ctor_set(v_reuseFailAlloc_337_, 18, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_337_, 19, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_337_, 20, v_proofs_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 21, v_propagate_329_);
lean_ctor_set_uint8(v_reuseFailAlloc_337_, sizeof(void*)*22, v_isCommRing_317_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed(lean_object* v_u_339_, lean_object* v_k_340_, lean_object* v___x_341_, lean_object* v_v_342_, lean_object* v_s_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(v_u_339_, v_k_340_, v___x_341_, v_v_342_, v_s_343_);
lean_dec(v___x_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object* v_u_345_, lean_object* v_v_346_, lean_object* v_k_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___f_352_; lean_object* v___x_353_; 
v___x_351_ = lean_box(0);
v___f_352_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_352_, 0, v_u_345_);
lean_closure_set(v___f_352_, 1, v_k_347_);
lean_closure_set(v___f_352_, 2, v___x_351_);
lean_closure_set(v___f_352_, 3, v_v_346_);
v___x_353_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_352_, v_a_348_, v_a_349_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object* v_u_354_, lean_object* v_v_355_, lean_object* v_k_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_354_, v_v_355_, v_k_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object* v_u_361_, lean_object* v_v_362_, lean_object* v_k_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_361_, v_v_362_, v_k_363_, v_a_364_, v_a_365_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object* v_u_377_, lean_object* v_v_378_, lean_object* v_k_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(v_u_377_, v_v_378_, v_k_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object* v_00_u03b2_393_, lean_object* v_m_394_, lean_object* v_k_395_, lean_object* v_v_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_m_394_, v_k_395_, v_v_396_);
return v___x_397_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object* v_00_u03b2_398_, lean_object* v_a_399_, lean_object* v_x_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_399_, v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_402_, lean_object* v_a_403_, lean_object* v_x_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(v_00_u03b2_402_, v_a_403_, v_x_404_);
lean_dec(v_x_404_);
lean_dec(v_a_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object* v_00_u03b2_407_, lean_object* v_a_408_, lean_object* v_b_409_, lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_408_, v_b_409_, v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object* v_u_412_, lean_object* v_k_413_, lean_object* v_inst_414_, lean_object* v_x_415_, size_t v_x_416_, size_t v_x_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(v_u_412_, v_k_413_, v_x_415_, v_x_416_, v_x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object* v_u_419_, lean_object* v_k_420_, lean_object* v_inst_421_, lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
size_t v_x_518__boxed_425_; size_t v_x_519__boxed_426_; lean_object* v_res_427_; 
v_x_518__boxed_425_ = lean_unbox_usize(v_x_423_);
lean_dec(v_x_423_);
v_x_519__boxed_426_ = lean_unbox_usize(v_x_424_);
lean_dec(v_x_424_);
v_res_427_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_419_, v_k_420_, v_inst_421_, v_x_422_, v_x_518__boxed_425_, v_x_519__boxed_426_);
lean_dec(v_inst_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(lean_object* v_v_428_, lean_object* v_p_429_, lean_object* v_x_430_, size_t v_x_431_, size_t v_x_432_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_cs_433_; size_t v_j_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_cs_433_ = lean_ctor_get(v_x_430_, 0);
v_j_434_ = lean_usize_shift_right(v_x_431_, v_x_432_);
v___x_435_ = lean_usize_to_nat(v_j_434_);
v___x_436_ = lean_array_get_size(v_cs_433_);
v___x_437_ = lean_nat_dec_lt(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_dec(v___x_435_);
lean_dec_ref(v_p_429_);
lean_dec(v_v_428_);
return v_x_430_;
}
else
{
lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_455_; 
lean_inc_ref(v_cs_433_);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_455_ == 0)
{
lean_object* v_unused_456_; 
v_unused_456_ = lean_ctor_get(v_x_430_, 0);
lean_dec(v_unused_456_);
v___x_439_ = v_x_430_;
v_isShared_440_ = v_isSharedCheck_455_;
goto v_resetjp_438_;
}
else
{
lean_dec(v_x_430_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_455_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
size_t v___x_441_; size_t v___x_442_; size_t v___x_443_; size_t v_i_444_; size_t v___x_445_; size_t v_shift_446_; lean_object* v_v_447_; lean_object* v___x_448_; lean_object* v_xs_x27_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_441_ = ((size_t)1ULL);
v___x_442_ = lean_usize_shift_left(v___x_441_, v_x_432_);
v___x_443_ = lean_usize_sub(v___x_442_, v___x_441_);
v_i_444_ = lean_usize_land(v_x_431_, v___x_443_);
v___x_445_ = ((size_t)5ULL);
v_shift_446_ = lean_usize_sub(v_x_432_, v___x_445_);
v_v_447_ = lean_array_fget(v_cs_433_, v___x_435_);
v___x_448_ = lean_box(0);
v_xs_x27_449_ = lean_array_fset(v_cs_433_, v___x_435_, v___x_448_);
v___x_450_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(v_v_428_, v_p_429_, v_v_447_, v_i_444_, v_shift_446_);
v___x_451_ = lean_array_fset(v_xs_x27_449_, v___x_435_, v___x_450_);
lean_dec(v___x_435_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_451_);
v___x_453_ = v___x_439_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_451_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_vs_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_vs_457_ = lean_ctor_get(v_x_430_, 0);
v___x_458_ = lean_usize_to_nat(v_x_431_);
v___x_459_ = lean_array_get_size(v_vs_457_);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v___x_458_);
lean_dec_ref(v_p_429_);
lean_dec(v_v_428_);
return v_x_430_;
}
else
{
lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_472_; 
lean_inc_ref(v_vs_457_);
v_isSharedCheck_472_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_472_ == 0)
{
lean_object* v_unused_473_; 
v_unused_473_ = lean_ctor_get(v_x_430_, 0);
lean_dec(v_unused_473_);
v___x_462_ = v_x_430_;
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
else
{
lean_dec(v_x_430_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_v_464_; lean_object* v___x_465_; lean_object* v_xs_x27_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v_v_464_ = lean_array_fget(v_vs_457_, v___x_458_);
v___x_465_ = lean_box(0);
v_xs_x27_466_ = lean_array_fset(v_vs_457_, v___x_458_, v___x_465_);
v___x_467_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_464_, v_v_428_, v_p_429_);
v___x_468_ = lean_array_fset(v_xs_x27_466_, v___x_458_, v___x_467_);
lean_dec(v___x_458_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg___boxed(lean_object* v_v_474_, lean_object* v_p_475_, lean_object* v_x_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
size_t v_x_178__boxed_479_; size_t v_x_179__boxed_480_; lean_object* v_res_481_; 
v_x_178__boxed_479_ = lean_unbox_usize(v_x_477_);
lean_dec(v_x_477_);
v_x_179__boxed_480_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_res_481_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(v_v_474_, v_p_475_, v_x_476_, v_x_178__boxed_479_, v_x_179__boxed_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object* v_v_482_, lean_object* v_p_483_, lean_object* v_inst_484_, lean_object* v_t_485_, lean_object* v_i_486_){
_start:
{
lean_object* v_root_487_; lean_object* v_tail_488_; lean_object* v_size_489_; size_t v_shift_490_; lean_object* v_tailOff_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_515_; 
v_root_487_ = lean_ctor_get(v_t_485_, 0);
v_tail_488_ = lean_ctor_get(v_t_485_, 1);
v_size_489_ = lean_ctor_get(v_t_485_, 2);
v_shift_490_ = lean_ctor_get_usize(v_t_485_, 4);
v_tailOff_491_ = lean_ctor_get(v_t_485_, 3);
v_isSharedCheck_515_ = !lean_is_exclusive(v_t_485_);
if (v_isSharedCheck_515_ == 0)
{
v___x_493_ = v_t_485_;
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_tailOff_491_);
lean_inc(v_size_489_);
lean_inc(v_tail_488_);
lean_inc(v_root_487_);
lean_dec(v_t_485_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_515_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; 
v___x_495_ = lean_nat_dec_le(v_tailOff_491_, v_i_486_);
if (v___x_495_ == 0)
{
size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = lean_usize_of_nat(v_i_486_);
v___x_497_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(v_v_482_, v_p_483_, v_root_487_, v___x_496_, v_shift_490_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_tail_488_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_size_489_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_tailOff_491_);
lean_ctor_set_usize(v_reuseFailAlloc_500_, 4, v_shift_490_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_nat_sub(v_i_486_, v_tailOff_491_);
v___x_502_ = lean_array_get_size(v_tail_488_);
v___x_503_ = lean_nat_dec_lt(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
lean_dec(v___x_501_);
lean_dec_ref(v_p_483_);
lean_dec(v_v_482_);
if (v_isShared_494_ == 0)
{
v___x_505_ = v___x_493_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_root_487_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_tail_488_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v_size_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_tailOff_491_);
lean_ctor_set_usize(v_reuseFailAlloc_506_, 4, v_shift_490_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_v_507_; lean_object* v___x_508_; lean_object* v_xs_x27_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_v_507_ = lean_array_fget(v_tail_488_, v___x_501_);
v___x_508_ = lean_box(0);
v_xs_x27_509_ = lean_array_fset(v_tail_488_, v___x_501_, v___x_508_);
v___x_510_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_507_, v_v_482_, v_p_483_);
v___x_511_ = lean_array_fset(v_xs_x27_509_, v___x_501_, v___x_510_);
lean_dec(v___x_501_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_511_);
v___x_513_ = v___x_493_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_root_487_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_size_489_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_tailOff_491_);
lean_ctor_set_usize(v_reuseFailAlloc_514_, 4, v_shift_490_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object* v_v_516_, lean_object* v_p_517_, lean_object* v_inst_518_, lean_object* v_t_519_, lean_object* v_i_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_516_, v_p_517_, v_inst_518_, v_t_519_, v_i_520_);
lean_dec(v_i_520_);
lean_dec(v_inst_518_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object* v_v_522_, lean_object* v_p_523_, lean_object* v___x_524_, lean_object* v_u_525_, lean_object* v_s_526_){
_start:
{
lean_object* v_id_527_; lean_object* v_type_528_; lean_object* v_u_529_; lean_object* v_isPreorderInst_530_; lean_object* v_leInst_531_; lean_object* v_ltInst_x3f_532_; lean_object* v_isPartialInst_x3f_533_; lean_object* v_isLinearPreInst_x3f_534_; lean_object* v_lawfulOrderLTInst_x3f_535_; lean_object* v_ringId_x3f_536_; uint8_t v_isCommRing_537_; lean_object* v_ringInst_x3f_538_; lean_object* v_orderedRingInst_x3f_539_; lean_object* v_leFn_540_; lean_object* v_ltFn_x3f_541_; lean_object* v_nodes_542_; lean_object* v_nodeMap_543_; lean_object* v_cnstrs_544_; lean_object* v_cnstrsOf_545_; lean_object* v_sources_546_; lean_object* v_targets_547_; lean_object* v_proofs_548_; lean_object* v_propagate_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_557_; 
v_id_527_ = lean_ctor_get(v_s_526_, 0);
v_type_528_ = lean_ctor_get(v_s_526_, 1);
v_u_529_ = lean_ctor_get(v_s_526_, 2);
v_isPreorderInst_530_ = lean_ctor_get(v_s_526_, 3);
v_leInst_531_ = lean_ctor_get(v_s_526_, 4);
v_ltInst_x3f_532_ = lean_ctor_get(v_s_526_, 5);
v_isPartialInst_x3f_533_ = lean_ctor_get(v_s_526_, 6);
v_isLinearPreInst_x3f_534_ = lean_ctor_get(v_s_526_, 7);
v_lawfulOrderLTInst_x3f_535_ = lean_ctor_get(v_s_526_, 8);
v_ringId_x3f_536_ = lean_ctor_get(v_s_526_, 9);
v_isCommRing_537_ = lean_ctor_get_uint8(v_s_526_, sizeof(void*)*22);
v_ringInst_x3f_538_ = lean_ctor_get(v_s_526_, 10);
v_orderedRingInst_x3f_539_ = lean_ctor_get(v_s_526_, 11);
v_leFn_540_ = lean_ctor_get(v_s_526_, 12);
v_ltFn_x3f_541_ = lean_ctor_get(v_s_526_, 13);
v_nodes_542_ = lean_ctor_get(v_s_526_, 14);
v_nodeMap_543_ = lean_ctor_get(v_s_526_, 15);
v_cnstrs_544_ = lean_ctor_get(v_s_526_, 16);
v_cnstrsOf_545_ = lean_ctor_get(v_s_526_, 17);
v_sources_546_ = lean_ctor_get(v_s_526_, 18);
v_targets_547_ = lean_ctor_get(v_s_526_, 19);
v_proofs_548_ = lean_ctor_get(v_s_526_, 20);
v_propagate_549_ = lean_ctor_get(v_s_526_, 21);
v_isSharedCheck_557_ = !lean_is_exclusive(v_s_526_);
if (v_isSharedCheck_557_ == 0)
{
v___x_551_ = v_s_526_;
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_propagate_549_);
lean_inc(v_proofs_548_);
lean_inc(v_targets_547_);
lean_inc(v_sources_546_);
lean_inc(v_cnstrsOf_545_);
lean_inc(v_cnstrs_544_);
lean_inc(v_nodeMap_543_);
lean_inc(v_nodes_542_);
lean_inc(v_ltFn_x3f_541_);
lean_inc(v_leFn_540_);
lean_inc(v_orderedRingInst_x3f_539_);
lean_inc(v_ringInst_x3f_538_);
lean_inc(v_ringId_x3f_536_);
lean_inc(v_lawfulOrderLTInst_x3f_535_);
lean_inc(v_isLinearPreInst_x3f_534_);
lean_inc(v_isPartialInst_x3f_533_);
lean_inc(v_ltInst_x3f_532_);
lean_inc(v_leInst_531_);
lean_inc(v_isPreorderInst_530_);
lean_inc(v_u_529_);
lean_inc(v_type_528_);
lean_inc(v_id_527_);
lean_dec(v_s_526_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_557_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_522_, v_p_523_, v___x_524_, v_proofs_548_, v_u_525_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 20, v___x_553_);
v___x_555_ = v___x_551_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_id_527_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_type_528_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_u_529_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_isPreorderInst_530_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v_leInst_531_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_ltInst_x3f_532_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_isPartialInst_x3f_533_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_isLinearPreInst_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_lawfulOrderLTInst_x3f_535_);
lean_ctor_set(v_reuseFailAlloc_556_, 9, v_ringId_x3f_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 10, v_ringInst_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 11, v_orderedRingInst_x3f_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 12, v_leFn_540_);
lean_ctor_set(v_reuseFailAlloc_556_, 13, v_ltFn_x3f_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 14, v_nodes_542_);
lean_ctor_set(v_reuseFailAlloc_556_, 15, v_nodeMap_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 16, v_cnstrs_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 17, v_cnstrsOf_545_);
lean_ctor_set(v_reuseFailAlloc_556_, 18, v_sources_546_);
lean_ctor_set(v_reuseFailAlloc_556_, 19, v_targets_547_);
lean_ctor_set(v_reuseFailAlloc_556_, 20, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 21, v_propagate_549_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*22, v_isCommRing_537_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object* v_v_558_, lean_object* v_p_559_, lean_object* v___x_560_, lean_object* v_u_561_, lean_object* v_s_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(v_v_558_, v_p_559_, v___x_560_, v_u_561_, v_s_562_);
lean_dec(v_u_561_);
lean_dec(v___x_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object* v_u_564_, lean_object* v_v_565_, lean_object* v_p_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
v___x_570_ = lean_box(0);
v___f_571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_571_, 0, v_v_565_);
lean_closure_set(v___f_571_, 1, v_p_566_);
lean_closure_set(v___f_571_, 2, v___x_570_);
lean_closure_set(v___f_571_, 3, v_u_564_);
v___x_572_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_571_, v_a_567_, v_a_568_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object* v_u_573_, lean_object* v_v_574_, lean_object* v_p_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_573_, v_v_574_, v_p_575_, v_a_576_, v_a_577_);
lean_dec(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object* v_u_580_, lean_object* v_v_581_, lean_object* v_p_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_580_, v_v_581_, v_p_582_, v_a_583_, v_a_584_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object* v_u_596_, lean_object* v_v_597_, lean_object* v_p_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(v_u_596_, v_v_597_, v_p_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec(v_a_600_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object* v_v_612_, lean_object* v_p_613_, lean_object* v_inst_614_, lean_object* v_x_615_, size_t v_x_616_, size_t v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(v_v_612_, v_p_613_, v_x_615_, v_x_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object* v_v_619_, lean_object* v_p_620_, lean_object* v_inst_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
size_t v_x_375__boxed_625_; size_t v_x_376__boxed_626_; lean_object* v_res_627_; 
v_x_375__boxed_625_ = lean_unbox_usize(v_x_623_);
lean_dec(v_x_623_);
v_x_376__boxed_626_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_627_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_619_, v_p_620_, v_inst_621_, v_x_622_, v_x_375__boxed_625_, v_x_376__boxed_626_);
lean_dec(v_inst_621_);
return v_res_627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0(void){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0);
v___x_630_ = l_ReaderT_instMonad___redArg(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object* v_u_635_, lean_object* v_f_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; lean_object* v_toApplicative_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_734_; 
v___x_649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_649_, 1);
lean_dec(v_unused_735_);
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_734_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_toApplicative_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_734_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_toFunctor_654_; lean_object* v_toSeq_655_; lean_object* v_toSeqLeft_656_; lean_object* v_toSeqRight_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_732_; 
v_toFunctor_654_ = lean_ctor_get(v_toApplicative_650_, 0);
v_toSeq_655_ = lean_ctor_get(v_toApplicative_650_, 2);
v_toSeqLeft_656_ = lean_ctor_get(v_toApplicative_650_, 3);
v_toSeqRight_657_ = lean_ctor_get(v_toApplicative_650_, 4);
v_isSharedCheck_732_ = !lean_is_exclusive(v_toApplicative_650_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_toApplicative_650_, 1);
lean_dec(v_unused_733_);
v___x_659_ = v_toApplicative_650_;
v_isShared_660_ = v_isSharedCheck_732_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_toSeqRight_657_);
lean_inc(v_toSeqLeft_656_);
lean_inc(v_toSeq_655_);
lean_inc(v_toFunctor_654_);
lean_dec(v_toApplicative_650_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_732_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___f_666_; lean_object* v___f_667_; lean_object* v___f_668_; lean_object* v___x_670_; 
v___f_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(v_toFunctor_654_);
v___f_663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_663_, 0, v_toFunctor_654_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_664_, 0, v_toFunctor_654_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___f_663_);
lean_ctor_set(v___x_665_, 1, v___f_664_);
v___f_666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_666_, 0, v_toSeqRight_657_);
v___f_667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_667_, 0, v_toSeqLeft_656_);
v___f_668_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_668_, 0, v_toSeq_655_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 4, v___f_666_);
lean_ctor_set(v___x_659_, 3, v___f_667_);
lean_ctor_set(v___x_659_, 2, v___f_668_);
lean_ctor_set(v___x_659_, 1, v___f_661_);
lean_ctor_set(v___x_659_, 0, v___x_665_);
v___x_670_ = v___x_659_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___f_661_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v___f_668_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v___f_667_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v___f_666_);
v___x_670_ = v_reuseFailAlloc_731_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_672_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___f_662_);
lean_ctor_set(v___x_652_, 0, v___x_670_);
v___x_672_ = v___x_652_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_670_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___f_662_);
v___x_672_ = v_reuseFailAlloc_730_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
lean_object* v___x_673_; lean_object* v_toApplicative_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_728_; 
v___x_673_ = l_ReaderT_instMonad___redArg(v___x_672_);
v_toApplicative_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; 
v_unused_729_ = lean_ctor_get(v___x_673_, 1);
lean_dec(v_unused_729_);
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_728_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_toApplicative_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_728_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_toFunctor_678_; lean_object* v_toSeq_679_; lean_object* v_toSeqLeft_680_; lean_object* v_toSeqRight_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_726_; 
v_toFunctor_678_ = lean_ctor_get(v_toApplicative_674_, 0);
v_toSeq_679_ = lean_ctor_get(v_toApplicative_674_, 2);
v_toSeqLeft_680_ = lean_ctor_get(v_toApplicative_674_, 3);
v_toSeqRight_681_ = lean_ctor_get(v_toApplicative_674_, 4);
v_isSharedCheck_726_ = !lean_is_exclusive(v_toApplicative_674_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_toApplicative_674_, 1);
lean_dec(v_unused_727_);
v___x_683_ = v_toApplicative_674_;
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_toSeqRight_681_);
lean_inc(v_toSeqLeft_680_);
lean_inc(v_toSeq_679_);
lean_inc(v_toFunctor_678_);
lean_dec(v_toApplicative_674_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_726_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___f_685_; lean_object* v___f_686_; lean_object* v___f_687_; lean_object* v___f_688_; lean_object* v___x_689_; lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___x_694_; 
v___f_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_678_);
v___f_687_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_687_, 0, v_toFunctor_678_);
v___f_688_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_688_, 0, v_toFunctor_678_);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___f_687_);
lean_ctor_set(v___x_689_, 1, v___f_688_);
v___f_690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_690_, 0, v_toSeqRight_681_);
v___f_691_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_691_, 0, v_toSeqLeft_680_);
v___f_692_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_692_, 0, v_toSeq_679_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 4, v___f_690_);
lean_ctor_set(v___x_683_, 3, v___f_691_);
lean_ctor_set(v___x_683_, 2, v___f_692_);
lean_ctor_set(v___x_683_, 1, v___f_685_);
lean_ctor_set(v___x_683_, 0, v___x_689_);
v___x_694_ = v___x_683_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___f_685_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v___f_692_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v___f_691_);
lean_ctor_set(v_reuseFailAlloc_725_, 4, v___f_690_);
v___x_694_ = v_reuseFailAlloc_725_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___f_686_);
lean_ctor_set(v___x_676_, 0, v___x_694_);
v___x_696_ = v___x_676_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___f_686_);
v___x_696_ = v_reuseFailAlloc_724_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_697_ = l_ReaderT_instMonad___redArg(v___x_696_);
v___x_698_ = l_ReaderT_instMonad___redArg(v___x_697_);
v___x_699_ = l_ReaderT_instMonad___redArg(v___x_698_);
v___x_700_ = l_ReaderT_instMonad___redArg(v___x_699_);
v___x_701_ = l_ReaderT_instMonad___redArg(v___x_700_);
v___x_702_ = l_ReaderT_instMonad___redArg(v___x_701_);
v___x_703_ = l_ReaderT_instMonad___redArg(v___x_702_);
v___x_704_ = l_Lean_Meta_Grind_Order_getStruct(v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_sources_706_; lean_object* v_size_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
v_sources_706_ = lean_ctor_get(v_a_705_, 18);
lean_inc_ref(v_sources_706_);
lean_dec(v_a_705_);
v_size_707_ = lean_ctor_get(v_sources_706_, 2);
v___x_708_ = lean_box(0);
v___x_709_ = lean_nat_dec_lt(v_u_635_, v_size_707_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_761__overap_711_; lean_object* v___x_712_; 
lean_dec_ref(v_sources_706_);
v___x_710_ = l_outOfBounds___redArg(v___x_708_);
v___x_761__overap_711_ = l_Lean_AssocList_forM___redArg(v___x_703_, v_f_636_, v___x_710_);
v___x_712_ = lean_apply_12(v___x_761__overap_711_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, lean_box(0));
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_759__overap_714_; lean_object* v___x_715_; 
v___x_713_ = l_Lean_PersistentArray_get_x21___redArg(v___x_708_, v_sources_706_, v_u_635_);
v___x_759__overap_714_ = l_Lean_AssocList_forM___redArg(v___x_703_, v_f_636_, v___x_713_);
v___x_715_ = lean_apply_12(v___x_759__overap_714_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, lean_box(0));
return v___x_715_;
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v___x_703_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
lean_dec_ref(v_f_636_);
v_a_716_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_704_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_704_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object* v_u_736_, lean_object* v_f_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(v_u_736_, v_f_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_u_736_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object* v_u_751_, lean_object* v_f_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v_toApplicative_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_850_; 
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_765_, 1);
lean_dec(v_unused_851_);
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_850_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_toApplicative_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_850_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_toFunctor_770_; lean_object* v_toSeq_771_; lean_object* v_toSeqLeft_772_; lean_object* v_toSeqRight_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_848_; 
v_toFunctor_770_ = lean_ctor_get(v_toApplicative_766_, 0);
v_toSeq_771_ = lean_ctor_get(v_toApplicative_766_, 2);
v_toSeqLeft_772_ = lean_ctor_get(v_toApplicative_766_, 3);
v_toSeqRight_773_ = lean_ctor_get(v_toApplicative_766_, 4);
v_isSharedCheck_848_ = !lean_is_exclusive(v_toApplicative_766_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_toApplicative_766_, 1);
lean_dec(v_unused_849_);
v___x_775_ = v_toApplicative_766_;
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_toSeqRight_773_);
lean_inc(v_toSeqLeft_772_);
lean_inc(v_toSeq_771_);
lean_inc(v_toFunctor_770_);
lean_dec(v_toApplicative_766_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___f_780_; lean_object* v___x_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_786_; 
v___f_777_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(v_toFunctor_770_);
v___f_779_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_779_, 0, v_toFunctor_770_);
v___f_780_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_780_, 0, v_toFunctor_770_);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___f_779_);
lean_ctor_set(v___x_781_, 1, v___f_780_);
v___f_782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_782_, 0, v_toSeqRight_773_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_783_, 0, v_toSeqLeft_772_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_784_, 0, v_toSeq_771_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 4, v___f_782_);
lean_ctor_set(v___x_775_, 3, v___f_783_);
lean_ctor_set(v___x_775_, 2, v___f_784_);
lean_ctor_set(v___x_775_, 1, v___f_777_);
lean_ctor_set(v___x_775_, 0, v___x_781_);
v___x_786_ = v___x_775_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_847_, 2, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_847_, 3, v___f_783_);
lean_ctor_set(v_reuseFailAlloc_847_, 4, v___f_782_);
v___x_786_ = v_reuseFailAlloc_847_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___f_778_);
lean_ctor_set(v___x_768_, 0, v___x_786_);
v___x_788_ = v___x_768_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___f_778_);
v___x_788_ = v_reuseFailAlloc_846_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_789_; lean_object* v_toApplicative_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_844_; 
v___x_789_ = l_ReaderT_instMonad___redArg(v___x_788_);
v_toApplicative_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v___x_789_, 1);
lean_dec(v_unused_845_);
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_844_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_toApplicative_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_844_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_toFunctor_794_; lean_object* v_toSeq_795_; lean_object* v_toSeqLeft_796_; lean_object* v_toSeqRight_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_842_; 
v_toFunctor_794_ = lean_ctor_get(v_toApplicative_790_, 0);
v_toSeq_795_ = lean_ctor_get(v_toApplicative_790_, 2);
v_toSeqLeft_796_ = lean_ctor_get(v_toApplicative_790_, 3);
v_toSeqRight_797_ = lean_ctor_get(v_toApplicative_790_, 4);
v_isSharedCheck_842_ = !lean_is_exclusive(v_toApplicative_790_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_dec(v_unused_843_);
v___x_799_ = v_toApplicative_790_;
v_isShared_800_ = v_isSharedCheck_842_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_toSeqRight_797_);
lean_inc(v_toSeqLeft_796_);
lean_inc(v_toSeq_795_);
lean_inc(v_toFunctor_794_);
lean_dec(v_toApplicative_790_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_842_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_810_; 
v___f_801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_794_);
v___f_803_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_803_, 0, v_toFunctor_794_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_804_, 0, v_toFunctor_794_);
v___x_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_805_, 0, v___f_803_);
lean_ctor_set(v___x_805_, 1, v___f_804_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeqRight_797_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_807_, 0, v_toSeqLeft_796_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_808_, 0, v_toSeq_795_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 4, v___f_806_);
lean_ctor_set(v___x_799_, 3, v___f_807_);
lean_ctor_set(v___x_799_, 2, v___f_808_);
lean_ctor_set(v___x_799_, 1, v___f_801_);
lean_ctor_set(v___x_799_, 0, v___x_805_);
v___x_810_ = v___x_799_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___f_801_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v___f_808_);
lean_ctor_set(v_reuseFailAlloc_841_, 3, v___f_807_);
lean_ctor_set(v_reuseFailAlloc_841_, 4, v___f_806_);
v___x_810_ = v_reuseFailAlloc_841_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___f_802_);
lean_ctor_set(v___x_792_, 0, v___x_810_);
v___x_812_ = v___x_792_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___f_802_);
v___x_812_ = v_reuseFailAlloc_840_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_813_ = l_ReaderT_instMonad___redArg(v___x_812_);
v___x_814_ = l_ReaderT_instMonad___redArg(v___x_813_);
v___x_815_ = l_ReaderT_instMonad___redArg(v___x_814_);
v___x_816_ = l_ReaderT_instMonad___redArg(v___x_815_);
v___x_817_ = l_ReaderT_instMonad___redArg(v___x_816_);
v___x_818_ = l_ReaderT_instMonad___redArg(v___x_817_);
v___x_819_ = l_ReaderT_instMonad___redArg(v___x_818_);
v___x_820_ = l_Lean_Meta_Grind_Order_getStruct(v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_targets_822_; lean_object* v_size_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
v_targets_822_ = lean_ctor_get(v_a_821_, 19);
lean_inc_ref(v_targets_822_);
lean_dec(v_a_821_);
v_size_823_ = lean_ctor_get(v_targets_822_, 2);
v___x_824_ = lean_box(0);
v___x_825_ = lean_nat_dec_lt(v_u_751_, v_size_823_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_761__overap_827_; lean_object* v___x_828_; 
lean_dec_ref(v_targets_822_);
v___x_826_ = l_outOfBounds___redArg(v___x_824_);
v___x_761__overap_827_ = l_Lean_AssocList_forM___redArg(v___x_819_, v_f_752_, v___x_826_);
v___x_828_ = lean_apply_12(v___x_761__overap_827_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, lean_box(0));
return v___x_828_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_759__overap_830_; lean_object* v___x_831_; 
v___x_829_ = l_Lean_PersistentArray_get_x21___redArg(v___x_824_, v_targets_822_, v_u_751_);
v___x_759__overap_830_ = l_Lean_AssocList_forM___redArg(v___x_819_, v_f_752_, v___x_829_);
v___x_831_ = lean_apply_12(v___x_759__overap_830_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, lean_box(0));
return v___x_831_;
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v___x_819_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_f_752_);
v_a_832_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_820_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_820_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object* v_u_852_, lean_object* v_f_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(v_u_852_, v_f_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_u_852_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_867_, lean_object* v_v_868_, lean_object* v_k_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_867_, v_v_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_898_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_898_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_898_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_a_883_) == 1)
{
lean_object* v_val_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_891_; 
v_val_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_val_887_);
lean_dec_ref(v_a_883_);
v___x_888_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_k_869_, v_val_887_);
lean_dec(v_val_887_);
v___x_889_ = lean_box(v___x_888_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_891_ = v___x_885_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
else
{
uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
lean_dec(v_a_883_);
v___x_893_ = 1;
v___x_894_ = lean_box(v___x_893_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_894_);
v___x_896_ = v___x_885_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_882_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_882_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_907_, lean_object* v_v_908_, lean_object* v_k_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_907_, v_v_908_, v_k_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_k_909_);
lean_dec(v_v_908_);
lean_dec(v_u_907_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_options_929_; uint8_t v_hasTrace_930_; 
v_options_929_ = lean_ctor_get(v___y_927_, 2);
v_hasTrace_930_ = lean_ctor_get_uint8(v_options_929_, sizeof(void*)*1);
if (v_hasTrace_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_cls_926_);
v___x_931_ = lean_box(v_hasTrace_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
else
{
lean_object* v_inheritedTraceOptions_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_inheritedTraceOptions_933_ = lean_ctor_get(v___y_927_, 13);
v___x_934_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_935_ = l_Lean_Name_append(v___x_934_, v_cls_926_);
v___x_936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_933_, v_options_929_, v___x_935_);
lean_dec(v___x_935_);
v___x_937_ = lean_box(v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_939_, v___y_940_);
lean_dec_ref(v___y_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_943_, v___y_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v___y_958_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_971_, lean_object* v_s_972_){
_start:
{
lean_object* v_id_973_; lean_object* v_type_974_; lean_object* v_u_975_; lean_object* v_isPreorderInst_976_; lean_object* v_leInst_977_; lean_object* v_ltInst_x3f_978_; lean_object* v_isPartialInst_x3f_979_; lean_object* v_isLinearPreInst_x3f_980_; lean_object* v_lawfulOrderLTInst_x3f_981_; lean_object* v_ringId_x3f_982_; uint8_t v_isCommRing_983_; lean_object* v_ringInst_x3f_984_; lean_object* v_orderedRingInst_x3f_985_; lean_object* v_leFn_986_; lean_object* v_ltFn_x3f_987_; lean_object* v_nodes_988_; lean_object* v_nodeMap_989_; lean_object* v_cnstrs_990_; lean_object* v_cnstrsOf_991_; lean_object* v_sources_992_; lean_object* v_targets_993_; lean_object* v_proofs_994_; lean_object* v_propagate_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1003_; 
v_id_973_ = lean_ctor_get(v_s_972_, 0);
v_type_974_ = lean_ctor_get(v_s_972_, 1);
v_u_975_ = lean_ctor_get(v_s_972_, 2);
v_isPreorderInst_976_ = lean_ctor_get(v_s_972_, 3);
v_leInst_977_ = lean_ctor_get(v_s_972_, 4);
v_ltInst_x3f_978_ = lean_ctor_get(v_s_972_, 5);
v_isPartialInst_x3f_979_ = lean_ctor_get(v_s_972_, 6);
v_isLinearPreInst_x3f_980_ = lean_ctor_get(v_s_972_, 7);
v_lawfulOrderLTInst_x3f_981_ = lean_ctor_get(v_s_972_, 8);
v_ringId_x3f_982_ = lean_ctor_get(v_s_972_, 9);
v_isCommRing_983_ = lean_ctor_get_uint8(v_s_972_, sizeof(void*)*22);
v_ringInst_x3f_984_ = lean_ctor_get(v_s_972_, 10);
v_orderedRingInst_x3f_985_ = lean_ctor_get(v_s_972_, 11);
v_leFn_986_ = lean_ctor_get(v_s_972_, 12);
v_ltFn_x3f_987_ = lean_ctor_get(v_s_972_, 13);
v_nodes_988_ = lean_ctor_get(v_s_972_, 14);
v_nodeMap_989_ = lean_ctor_get(v_s_972_, 15);
v_cnstrs_990_ = lean_ctor_get(v_s_972_, 16);
v_cnstrsOf_991_ = lean_ctor_get(v_s_972_, 17);
v_sources_992_ = lean_ctor_get(v_s_972_, 18);
v_targets_993_ = lean_ctor_get(v_s_972_, 19);
v_proofs_994_ = lean_ctor_get(v_s_972_, 20);
v_propagate_995_ = lean_ctor_get(v_s_972_, 21);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_s_972_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_997_ = v_s_972_;
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_propagate_995_);
lean_inc(v_proofs_994_);
lean_inc(v_targets_993_);
lean_inc(v_sources_992_);
lean_inc(v_cnstrsOf_991_);
lean_inc(v_cnstrs_990_);
lean_inc(v_nodeMap_989_);
lean_inc(v_nodes_988_);
lean_inc(v_ltFn_x3f_987_);
lean_inc(v_leFn_986_);
lean_inc(v_orderedRingInst_x3f_985_);
lean_inc(v_ringInst_x3f_984_);
lean_inc(v_ringId_x3f_982_);
lean_inc(v_lawfulOrderLTInst_x3f_981_);
lean_inc(v_isLinearPreInst_x3f_980_);
lean_inc(v_isPartialInst_x3f_979_);
lean_inc(v_ltInst_x3f_978_);
lean_inc(v_leInst_977_);
lean_inc(v_isPreorderInst_976_);
lean_inc(v_u_975_);
lean_inc(v_type_974_);
lean_inc(v_id_973_);
lean_dec(v_s_972_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1003_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_999_, 0, v_p_971_);
lean_ctor_set(v___x_999_, 1, v_propagate_995_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 21, v___x_999_);
v___x_1001_ = v___x_997_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_id_973_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_type_974_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_u_975_);
lean_ctor_set(v_reuseFailAlloc_1002_, 3, v_isPreorderInst_976_);
lean_ctor_set(v_reuseFailAlloc_1002_, 4, v_leInst_977_);
lean_ctor_set(v_reuseFailAlloc_1002_, 5, v_ltInst_x3f_978_);
lean_ctor_set(v_reuseFailAlloc_1002_, 6, v_isPartialInst_x3f_979_);
lean_ctor_set(v_reuseFailAlloc_1002_, 7, v_isLinearPreInst_x3f_980_);
lean_ctor_set(v_reuseFailAlloc_1002_, 8, v_lawfulOrderLTInst_x3f_981_);
lean_ctor_set(v_reuseFailAlloc_1002_, 9, v_ringId_x3f_982_);
lean_ctor_set(v_reuseFailAlloc_1002_, 10, v_ringInst_x3f_984_);
lean_ctor_set(v_reuseFailAlloc_1002_, 11, v_orderedRingInst_x3f_985_);
lean_ctor_set(v_reuseFailAlloc_1002_, 12, v_leFn_986_);
lean_ctor_set(v_reuseFailAlloc_1002_, 13, v_ltFn_x3f_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 14, v_nodes_988_);
lean_ctor_set(v_reuseFailAlloc_1002_, 15, v_nodeMap_989_);
lean_ctor_set(v_reuseFailAlloc_1002_, 16, v_cnstrs_990_);
lean_ctor_set(v_reuseFailAlloc_1002_, 17, v_cnstrsOf_991_);
lean_ctor_set(v_reuseFailAlloc_1002_, 18, v_sources_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 19, v_targets_993_);
lean_ctor_set(v_reuseFailAlloc_1002_, 20, v_proofs_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 21, v___x_999_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*22, v_isCommRing_983_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(lean_object* v_msgData_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; lean_object* v_env_1011_; lean_object* v___x_1012_; lean_object* v_mctx_1013_; lean_object* v_lctx_1014_; lean_object* v_options_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1010_ = lean_st_ref_get(v___y_1008_);
v_env_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc_ref(v_env_1011_);
lean_dec(v___x_1010_);
v___x_1012_ = lean_st_ref_get(v___y_1006_);
v_mctx_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc_ref(v_mctx_1013_);
lean_dec(v___x_1012_);
v_lctx_1014_ = lean_ctor_get(v___y_1005_, 2);
v_options_1015_ = lean_ctor_get(v___y_1007_, 2);
lean_inc_ref(v_options_1015_);
lean_inc_ref(v_lctx_1014_);
v___x_1016_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1016_, 0, v_env_1011_);
lean_ctor_set(v___x_1016_, 1, v_mctx_1013_);
lean_ctor_set(v___x_1016_, 2, v_lctx_1014_);
lean_ctor_set(v___x_1016_, 3, v_options_1015_);
v___x_1017_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_msgData_1004_);
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1___boxed(lean_object* v_msgData_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(v_msgData_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1026_; double v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_float_of_nat(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(lean_object* v_cls_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_ref_1038_; lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1084_; 
v_ref_1038_ = lean_ctor_get(v___y_1035_, 5);
v___x_1039_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1084_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1084_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v_traceState_1045_; lean_object* v_env_1046_; lean_object* v_nextMacroScope_1047_; lean_object* v_ngen_1048_; lean_object* v_auxDeclNGen_1049_; lean_object* v_cache_1050_; lean_object* v_messages_1051_; lean_object* v_infoState_1052_; lean_object* v_snapshotTasks_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1083_; 
v___x_1044_ = lean_st_ref_take(v___y_1036_);
v_traceState_1045_ = lean_ctor_get(v___x_1044_, 4);
v_env_1046_ = lean_ctor_get(v___x_1044_, 0);
v_nextMacroScope_1047_ = lean_ctor_get(v___x_1044_, 1);
v_ngen_1048_ = lean_ctor_get(v___x_1044_, 2);
v_auxDeclNGen_1049_ = lean_ctor_get(v___x_1044_, 3);
v_cache_1050_ = lean_ctor_get(v___x_1044_, 5);
v_messages_1051_ = lean_ctor_get(v___x_1044_, 6);
v_infoState_1052_ = lean_ctor_get(v___x_1044_, 7);
v_snapshotTasks_1053_ = lean_ctor_get(v___x_1044_, 8);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1055_ = v___x_1044_;
v_isShared_1056_ = v_isSharedCheck_1083_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_snapshotTasks_1053_);
lean_inc(v_infoState_1052_);
lean_inc(v_messages_1051_);
lean_inc(v_cache_1050_);
lean_inc(v_traceState_1045_);
lean_inc(v_auxDeclNGen_1049_);
lean_inc(v_ngen_1048_);
lean_inc(v_nextMacroScope_1047_);
lean_inc(v_env_1046_);
lean_dec(v___x_1044_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1083_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
uint64_t v_tid_1057_; lean_object* v_traces_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1082_; 
v_tid_1057_ = lean_ctor_get_uint64(v_traceState_1045_, sizeof(void*)*1);
v_traces_1058_ = lean_ctor_get(v_traceState_1045_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_traceState_1045_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1060_ = v_traceState_1045_;
v_isShared_1061_ = v_isSharedCheck_1082_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_traces_1058_);
lean_dec(v_traceState_1045_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1082_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; double v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1062_ = lean_box(0);
v___x_1063_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0);
v___x_1064_ = 0;
v___x_1065_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1));
v___x_1066_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1066_, 0, v_cls_1031_);
lean_ctor_set(v___x_1066_, 1, v___x_1062_);
lean_ctor_set(v___x_1066_, 2, v___x_1065_);
lean_ctor_set_float(v___x_1066_, sizeof(void*)*3, v___x_1063_);
lean_ctor_set_float(v___x_1066_, sizeof(void*)*3 + 8, v___x_1063_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*3 + 16, v___x_1064_);
v___x_1067_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2));
v___x_1068_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v_a_1040_);
lean_ctor_set(v___x_1068_, 2, v___x_1067_);
lean_inc(v_ref_1038_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_ref_1038_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_PersistentArray_push___redArg(v_traces_1058_, v___x_1069_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 0, v___x_1070_);
v___x_1072_ = v___x_1060_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1070_);
lean_ctor_set_uint64(v_reuseFailAlloc_1081_, sizeof(void*)*1, v_tid_1057_);
v___x_1072_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v___x_1072_);
v___x_1074_ = v___x_1055_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_env_1046_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_nextMacroScope_1047_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_ngen_1048_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_auxDeclNGen_1049_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_cache_1050_);
lean_ctor_set(v_reuseFailAlloc_1080_, 6, v_messages_1051_);
lean_ctor_set(v_reuseFailAlloc_1080_, 7, v_infoState_1052_);
lean_ctor_set(v_reuseFailAlloc_1080_, 8, v_snapshotTasks_1053_);
v___x_1074_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1075_ = lean_st_ref_set(v___y_1036_, v___x_1074_);
v___x_1076_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1076_);
v___x_1078_ = v___x_1042_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___boxed(lean_object* v_cls_1085_, lean_object* v_msg_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v_cls_1085_, v_msg_1086_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_cls_1115_; lean_object* v___x_1116_; lean_object* v_a_1117_; lean_object* v___f_1118_; uint8_t v___x_1119_; 
v_cls_1115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_1116_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1115_, v_a_1112_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
lean_inc_ref(v_p_1102_);
v___f_1118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_1118_, 0, v_p_1102_);
v___x_1119_ = lean_unbox(v_a_1117_);
lean_dec(v_a_1117_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref(v_p_1102_);
v___x_1120_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1118_, v_a_1103_, v_a_1104_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_p_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1123_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref(v___x_1121_);
v___x_1123_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v_cls_1115_, v_a_1122_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1123_);
v___x_1124_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1118_, v_a_1103_, v_a_1104_);
return v___x_1124_;
}
else
{
lean_dec_ref(v___f_1118_);
lean_dec(v_a_1103_);
return v___x_1123_;
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec_ref(v___f_1118_);
lean_dec(v_a_1103_);
v_a_1125_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1121_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1121_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec(v_a_1135_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(lean_object* v_cls_1147_, lean_object* v_msg_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v_cls_1147_, v_msg_1148_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___boxed(lean_object* v_cls_1162_, lean_object* v_msg_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(v_cls_1162_, v_msg_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec(v___y_1164_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1177_, lean_object* v_vals_1178_, lean_object* v_i_1179_, lean_object* v_k_1180_){
_start:
{
lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1181_ = lean_array_get_size(v_keys_1177_);
v___x_1182_ = lean_nat_dec_lt(v_i_1179_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_i_1179_);
v___x_1183_ = lean_box(0);
return v___x_1183_;
}
else
{
lean_object* v_k_x27_1184_; uint8_t v___x_1185_; 
v_k_x27_1184_ = lean_array_fget_borrowed(v_keys_1177_, v_i_1179_);
v___x_1185_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1180_, v_k_x27_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_i_1179_, v___x_1186_);
lean_dec(v_i_1179_);
v_i_1179_ = v___x_1187_;
goto _start;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_array_fget_borrowed(v_vals_1178_, v_i_1179_);
lean_dec(v_i_1179_);
lean_inc(v___x_1189_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1191_, lean_object* v_vals_1192_, lean_object* v_i_1193_, lean_object* v_k_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1191_, v_vals_1192_, v_i_1193_, v_k_1194_);
lean_dec_ref(v_k_1194_);
lean_dec_ref(v_vals_1192_);
lean_dec_ref(v_keys_1191_);
return v_res_1195_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1196_; size_t v___x_1197_; size_t v___x_1198_; 
v___x_1196_ = ((size_t)5ULL);
v___x_1197_ = ((size_t)1ULL);
v___x_1198_ = lean_usize_shift_left(v___x_1197_, v___x_1196_);
return v___x_1198_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1199_; size_t v___x_1200_; size_t v___x_1201_; 
v___x_1199_ = ((size_t)1ULL);
v___x_1200_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0);
v___x_1201_ = lean_usize_sub(v___x_1200_, v___x_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1202_, size_t v_x_1203_, lean_object* v_x_1204_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v_es_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1226_; 
v_es_1205_ = lean_ctor_get(v_x_1202_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_x_1202_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1207_ = v_x_1202_;
v_isShared_1208_ = v_isSharedCheck_1226_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_es_1205_);
lean_dec(v_x_1202_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1226_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; size_t v___x_1210_; size_t v___x_1211_; size_t v___x_1212_; lean_object* v_j_1213_; lean_object* v___x_1214_; 
v___x_1209_ = lean_box(2);
v___x_1210_ = ((size_t)5ULL);
v___x_1211_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1);
v___x_1212_ = lean_usize_land(v_x_1203_, v___x_1211_);
v_j_1213_ = lean_usize_to_nat(v___x_1212_);
v___x_1214_ = lean_array_get(v___x_1209_, v_es_1205_, v_j_1213_);
lean_dec(v_j_1213_);
lean_dec_ref(v_es_1205_);
switch(lean_obj_tag(v___x_1214_))
{
case 0:
{
lean_object* v_key_1215_; lean_object* v_val_1216_; uint8_t v___x_1217_; 
v_key_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_key_1215_);
v_val_1216_ = lean_ctor_get(v___x_1214_, 1);
lean_inc(v_val_1216_);
lean_dec_ref(v___x_1214_);
v___x_1217_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1204_, v_key_1215_);
lean_dec(v_key_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec(v_val_1216_);
lean_del_object(v___x_1207_);
v___x_1218_ = lean_box(0);
return v___x_1218_;
}
else
{
lean_object* v___x_1220_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set_tag(v___x_1207_, 1);
lean_ctor_set(v___x_1207_, 0, v_val_1216_);
v___x_1220_ = v___x_1207_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_val_1216_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
case 1:
{
lean_object* v_node_1222_; size_t v___x_1223_; 
lean_del_object(v___x_1207_);
v_node_1222_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_node_1222_);
lean_dec_ref(v___x_1214_);
v___x_1223_ = lean_usize_shift_right(v_x_1203_, v___x_1210_);
v_x_1202_ = v_node_1222_;
v_x_1203_ = v___x_1223_;
goto _start;
}
default: 
{
lean_object* v___x_1225_; 
lean_del_object(v___x_1207_);
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_ks_1227_; lean_object* v_vs_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_ks_1227_ = lean_ctor_get(v_x_1202_, 0);
lean_inc_ref(v_ks_1227_);
v_vs_1228_ = lean_ctor_get(v_x_1202_, 1);
lean_inc_ref(v_vs_1228_);
lean_dec_ref(v_x_1202_);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1227_, v_vs_1228_, v___x_1229_, v_x_1204_);
lean_dec_ref(v_vs_1228_);
lean_dec_ref(v_ks_1227_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
size_t v_x_9805__boxed_1234_; lean_object* v_res_1235_; 
v_x_9805__boxed_1234_ = lean_unbox_usize(v_x_1232_);
lean_dec(v_x_1232_);
v_res_1235_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1231_, v_x_9805__boxed_1234_, v_x_1233_);
lean_dec_ref(v_x_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
uint64_t v___x_1238_; size_t v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1237_);
v___x_1239_ = lean_uint64_to_usize(v___x_1238_);
v___x_1240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1236_, v___x_1239_, v_x_1237_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1241_, v_x_1242_);
lean_dec_ref(v_x_1242_);
return v_res_1243_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_box(0);
v___x_1254_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1255_ = l_Lean_mkConst(v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1256_, lean_object* v_e_1257_, lean_object* v_u_1258_, lean_object* v_v_1259_, lean_object* v_k_1260_, lean_object* v_k_x27_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v_h_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___x_1302_; 
v___x_1302_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1258_, v_v_1259_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref(v___x_1302_);
v___x_1304_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1258_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref(v___x_1304_);
v___x_1306_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1259_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1306_);
lean_inc(v_a_1272_);
lean_inc_ref(v_a_1271_);
lean_inc(v_a_1270_);
lean_inc_ref(v_a_1269_);
lean_inc_ref(v_a_1267_);
lean_inc_ref(v_a_1265_);
lean_inc(v_a_1263_);
v___x_1308_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1305_, v_a_1307_, v_k_1260_, v_a_1303_, v_k_x27_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_h_x3f_1309_; 
v_h_x3f_1309_ = lean_ctor_get(v_c_1256_, 4);
lean_inc(v_h_x3f_1309_);
if (lean_obj_tag(v_h_x3f_1309_) == 1)
{
lean_object* v_a_1310_; lean_object* v_e_1311_; lean_object* v_val_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v_a_1310_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1310_);
lean_dec_ref(v___x_1308_);
v_e_1311_ = lean_ctor_get(v_c_1256_, 3);
lean_inc_ref(v_e_1311_);
lean_dec_ref(v_c_1256_);
v_val_1312_ = lean_ctor_get(v_h_x3f_1309_, 0);
lean_inc(v_val_1312_);
lean_dec_ref(v_h_x3f_1309_);
v___x_1313_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1257_);
v___x_1314_ = l_Lean_mkApp4(v___x_1313_, v_e_1257_, v_e_1311_, v_val_1312_, v_a_1310_);
v_h_1275_ = v___x_1314_;
v___y_1276_ = v_a_1263_;
v___y_1277_ = v_a_1265_;
v___y_1278_ = v_a_1267_;
v___y_1279_ = v_a_1269_;
v___y_1280_ = v_a_1270_;
v___y_1281_ = v_a_1271_;
v___y_1282_ = v_a_1272_;
goto v___jp_1274_;
}
else
{
lean_object* v_a_1315_; 
lean_dec(v_h_x3f_1309_);
lean_dec_ref(v_c_1256_);
v_a_1315_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1315_);
lean_dec_ref(v___x_1308_);
v_h_1275_ = v_a_1315_;
v___y_1276_ = v_a_1263_;
v___y_1277_ = v_a_1265_;
v___y_1278_ = v_a_1267_;
v___y_1279_ = v_a_1269_;
v___y_1280_ = v_a_1270_;
v___y_1281_ = v_a_1271_;
v___y_1282_ = v_a_1272_;
goto v___jp_1274_;
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec_ref(v_a_1267_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1263_);
lean_dec_ref(v_e_1257_);
lean_dec_ref(v_c_1256_);
v_a_1316_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1308_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1308_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_a_1305_);
lean_dec(v_a_1303_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_e_1257_);
lean_dec_ref(v_c_1256_);
v_a_1324_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1306_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1306_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec(v_a_1303_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_e_1257_);
lean_dec_ref(v_c_1256_);
v_a_1332_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1304_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1304_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
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
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_e_1257_);
lean_dec_ref(v_c_1256_);
v_a_1340_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1302_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1302_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
v___jp_1274_:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1276_, v___y_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_termMapInv_1285_; lean_object* v___x_1286_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v_termMapInv_1285_ = lean_ctor_get(v_a_1284_, 4);
lean_inc_ref(v_termMapInv_1285_);
lean_dec(v_a_1284_);
v___x_1286_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1285_, v_e_1257_);
if (lean_obj_tag(v___x_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1287_);
lean_dec_ref(v___x_1286_);
v_fst_1288_ = lean_ctor_get(v_val_1287_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v_val_1287_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_val_1287_);
v___x_1290_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc(v_fst_1288_);
v___x_1291_ = l_Lean_mkApp4(v___x_1290_, v_fst_1288_, v_e_1257_, v_snd_1289_, v_h_1275_);
v___x_1292_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1288_, v___x_1291_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
lean_dec(v___x_1286_);
v___x_1293_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1257_, v_h_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
return v___x_1293_;
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v_h_1275_);
lean_dec_ref(v_e_1257_);
v_a_1294_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1283_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1348_ = _args[0];
lean_object* v_e_1349_ = _args[1];
lean_object* v_u_1350_ = _args[2];
lean_object* v_v_1351_ = _args[3];
lean_object* v_k_1352_ = _args[4];
lean_object* v_k_x27_1353_ = _args[5];
lean_object* v_a_1354_ = _args[6];
lean_object* v_a_1355_ = _args[7];
lean_object* v_a_1356_ = _args[8];
lean_object* v_a_1357_ = _args[9];
lean_object* v_a_1358_ = _args[10];
lean_object* v_a_1359_ = _args[11];
lean_object* v_a_1360_ = _args[12];
lean_object* v_a_1361_ = _args[13];
lean_object* v_a_1362_ = _args[14];
lean_object* v_a_1363_ = _args[15];
lean_object* v_a_1364_ = _args[16];
lean_object* v_a_1365_ = _args[17];
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1348_, v_e_1349_, v_u_1350_, v_v_1351_, v_k_1352_, v_k_x27_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_);
lean_dec_ref(v_k_x27_1353_);
lean_dec_ref(v_k_1352_);
lean_dec(v_v_1351_);
lean_dec(v_u_1350_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1367_, lean_object* v_x_1368_, lean_object* v_x_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1368_, v_x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1371_, v_x_1372_, v_x_1373_);
lean_dec_ref(v_x_1373_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1375_, lean_object* v_x_1376_, size_t v_x_1377_, lean_object* v_x_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1376_, v_x_1377_, v_x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
size_t v_x_10114__boxed_1384_; lean_object* v_res_1385_; 
v_x_10114__boxed_1384_ = lean_unbox_usize(v_x_1382_);
lean_dec(v_x_1382_);
v_res_1385_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1380_, v_x_1381_, v_x_10114__boxed_1384_, v_x_1383_);
lean_dec_ref(v_x_1383_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1386_, lean_object* v_keys_1387_, lean_object* v_vals_1388_, lean_object* v_heq_1389_, lean_object* v_i_1390_, lean_object* v_k_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1387_, v_vals_1388_, v_i_1390_, v_k_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1393_, lean_object* v_keys_1394_, lean_object* v_vals_1395_, lean_object* v_heq_1396_, lean_object* v_i_1397_, lean_object* v_k_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1393_, v_keys_1394_, v_vals_1395_, v_heq_1396_, v_i_1397_, v_k_1398_);
lean_dec_ref(v_k_1398_);
lean_dec_ref(v_vals_1395_);
lean_dec_ref(v_keys_1394_);
return v_res_1399_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; lean_object* v___f_1415_; lean_object* v___x_6298__overap_1416_; lean_object* v___x_1417_; 
v___x_1414_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1415_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1415_, 0, v___x_1414_);
v___x_6298__overap_1416_ = lean_panic_fn(v___f_1415_, v_msg_1401_);
v___x_1417_ = lean_apply_12(v___x_6298__overap_1416_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, lean_box(0));
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v_res_1431_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1435_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1436_ = lean_unsigned_to_nat(2u);
v___x_1437_ = lean_unsigned_to_nat(86u);
v___x_1438_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1439_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1440_ = l_mkPanicMessageWithDecl(v___x_1439_, v___x_1438_, v___x_1437_, v___x_1436_, v___x_1435_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1441_, lean_object* v_e_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_u_1455_; lean_object* v_v_1456_; lean_object* v_e_1457_; lean_object* v_h_x3f_1458_; lean_object* v___x_1459_; 
v_u_1455_ = lean_ctor_get(v_c_1441_, 0);
v_v_1456_ = lean_ctor_get(v_c_1441_, 1);
v_e_1457_ = lean_ctor_get(v_c_1441_, 3);
lean_inc_ref(v_e_1457_);
v_h_x3f_1458_ = lean_ctor_get(v_c_1441_, 4);
lean_inc(v_h_x3f_1458_);
v___x_1459_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1455_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; uint8_t v___x_1461_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = lean_nat_dec_eq(v_u_1455_, v_v_1456_);
if (v___x_1461_ == 0)
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec(v_a_1460_);
lean_dec(v_h_x3f_1458_);
lean_dec_ref(v_e_1457_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_c_1441_);
v___x_1462_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1463_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1462_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1441_);
lean_dec_ref(v_c_1441_);
lean_inc(v_a_1453_);
lean_inc_ref(v_a_1452_);
lean_inc(v_a_1451_);
lean_inc_ref(v_a_1450_);
lean_inc_ref(v_a_1448_);
lean_inc_ref(v_a_1446_);
lean_inc(v_a_1444_);
v___x_1465_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1460_, v___x_1464_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_);
lean_dec_ref(v___x_1464_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v_h_1468_; lean_object* v___y_1469_; lean_object* v___y_1470_; lean_object* v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref(v___x_1465_);
if (lean_obj_tag(v_h_x3f_1458_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_val_1495_ = lean_ctor_get(v_h_x3f_1458_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v_h_x3f_1458_);
v___x_1496_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1442_);
v___x_1497_ = l_Lean_mkApp4(v___x_1496_, v_e_1442_, v_e_1457_, v_val_1495_, v_a_1466_);
v_h_1468_ = v___x_1497_;
v___y_1469_ = v_a_1444_;
v___y_1470_ = v_a_1446_;
v___y_1471_ = v_a_1448_;
v___y_1472_ = v_a_1450_;
v___y_1473_ = v_a_1451_;
v___y_1474_ = v_a_1452_;
v___y_1475_ = v_a_1453_;
goto v___jp_1467_;
}
else
{
lean_dec(v_h_x3f_1458_);
lean_dec_ref(v_e_1457_);
v_h_1468_ = v_a_1466_;
v___y_1469_ = v_a_1444_;
v___y_1470_ = v_a_1446_;
v___y_1471_ = v_a_1448_;
v___y_1472_ = v_a_1450_;
v___y_1473_ = v_a_1451_;
v___y_1474_ = v_a_1452_;
v___y_1475_ = v_a_1453_;
goto v___jp_1467_;
}
v___jp_1467_:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1469_, v___y_1474_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v_termMapInv_1478_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v_termMapInv_1478_ = lean_ctor_get(v_a_1477_, 4);
lean_inc_ref(v_termMapInv_1478_);
lean_dec(v_a_1477_);
v___x_1479_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1478_, v_e_1442_);
if (lean_obj_tag(v___x_1479_) == 1)
{
lean_object* v_val_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_val_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_val_1480_);
lean_dec_ref(v___x_1479_);
v_fst_1481_ = lean_ctor_get(v_val_1480_, 0);
lean_inc(v_fst_1481_);
v_snd_1482_ = lean_ctor_get(v_val_1480_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_val_1480_);
v___x_1483_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc(v_fst_1481_);
v___x_1484_ = l_Lean_mkApp4(v___x_1483_, v_fst_1481_, v_e_1442_, v_snd_1482_, v_h_1468_);
v___x_1485_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1481_, v___x_1484_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; 
lean_dec(v___x_1479_);
v___x_1486_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1442_, v_h_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
return v___x_1486_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v_h_1468_);
lean_dec_ref(v_e_1442_);
v_a_1487_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1476_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1476_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_h_x3f_1458_);
lean_dec_ref(v_e_1457_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec_ref(v_a_1448_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1444_);
lean_dec_ref(v_e_1442_);
v_a_1498_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1465_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1465_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec(v_h_x3f_1458_);
lean_dec_ref(v_e_1457_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec(v_a_1451_);
lean_dec_ref(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_e_1442_);
lean_dec_ref(v_c_1441_);
v_a_1506_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1459_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1459_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1514_, lean_object* v_e_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1514_, v_e_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_box(0);
v___x_1536_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1537_ = l_Lean_mkConst(v___x_1536_, v___x_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1538_, lean_object* v_e_1539_, lean_object* v_u_1540_, lean_object* v_v_1541_, lean_object* v_k_1542_, lean_object* v_k_x27_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_h_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1540_, v_v_1541_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1540_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
v___x_1588_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1541_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1587_, v_a_1589_, v_k_1542_, v_a_1585_, v_k_x27_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_h_x3f_1591_; 
v_h_x3f_1591_ = lean_ctor_get(v_c_1538_, 4);
lean_inc(v_h_x3f_1591_);
if (lean_obj_tag(v_h_x3f_1591_) == 1)
{
lean_object* v_a_1592_; lean_object* v_e_1593_; lean_object* v_val_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_a_1592_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1590_);
v_e_1593_ = lean_ctor_get(v_c_1538_, 3);
lean_inc_ref(v_e_1593_);
lean_dec_ref(v_c_1538_);
v_val_1594_ = lean_ctor_get(v_h_x3f_1591_, 0);
lean_inc(v_val_1594_);
lean_dec_ref(v_h_x3f_1591_);
v___x_1595_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1539_);
v___x_1596_ = l_Lean_mkApp4(v___x_1595_, v_e_1539_, v_e_1593_, v_val_1594_, v_a_1592_);
v_h_1557_ = v___x_1596_;
v___y_1558_ = v_a_1545_;
v___y_1559_ = v_a_1547_;
v___y_1560_ = v_a_1549_;
v___y_1561_ = v_a_1551_;
v___y_1562_ = v_a_1552_;
v___y_1563_ = v_a_1553_;
v___y_1564_ = v_a_1554_;
goto v___jp_1556_;
}
else
{
lean_object* v_a_1597_; 
lean_dec(v_h_x3f_1591_);
lean_dec_ref(v_c_1538_);
v_a_1597_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1590_);
v_h_1557_ = v_a_1597_;
v___y_1558_ = v_a_1545_;
v___y_1559_ = v_a_1547_;
v___y_1560_ = v_a_1549_;
v___y_1561_ = v_a_1551_;
v___y_1562_ = v_a_1552_;
v___y_1563_ = v_a_1553_;
v___y_1564_ = v_a_1554_;
goto v___jp_1556_;
}
}
else
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1605_; 
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec_ref(v_e_1539_);
lean_dec_ref(v_c_1538_);
v_a_1598_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1600_ = v___x_1590_;
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1590_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1605_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1598_);
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
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_dec(v_a_1587_);
lean_dec(v_a_1585_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec_ref(v_e_1539_);
lean_dec_ref(v_c_1538_);
v_a_1606_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1588_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1588_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v_a_1585_);
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec_ref(v_e_1539_);
lean_dec_ref(v_c_1538_);
v_a_1614_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1586_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1586_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_a_1554_);
lean_dec_ref(v_a_1553_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec_ref(v_e_1539_);
lean_dec_ref(v_c_1538_);
v_a_1622_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1584_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1584_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
v___jp_1556_:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1558_, v___y_1563_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v_termMapInv_1567_; lean_object* v___x_1568_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1565_);
v_termMapInv_1567_ = lean_ctor_get(v_a_1566_, 4);
lean_inc_ref(v_termMapInv_1567_);
lean_dec(v_a_1566_);
v___x_1568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1567_, v_e_1539_);
if (lean_obj_tag(v___x_1568_) == 1)
{
lean_object* v_val_1569_; lean_object* v_fst_1570_; lean_object* v_snd_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_val_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v___x_1568_);
v_fst_1570_ = lean_ctor_get(v_val_1569_, 0);
lean_inc(v_fst_1570_);
v_snd_1571_ = lean_ctor_get(v_val_1569_, 1);
lean_inc(v_snd_1571_);
lean_dec(v_val_1569_);
v___x_1572_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc(v_fst_1570_);
v___x_1573_ = l_Lean_mkApp4(v___x_1572_, v_fst_1570_, v_e_1539_, v_snd_1571_, v_h_1557_);
v___x_1574_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1570_, v___x_1573_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1574_;
}
else
{
lean_object* v___x_1575_; 
lean_dec(v___x_1568_);
v___x_1575_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1539_, v_h_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
return v___x_1575_;
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec_ref(v_h_1557_);
lean_dec_ref(v_e_1539_);
v_a_1576_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1565_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1565_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1630_ = _args[0];
lean_object* v_e_1631_ = _args[1];
lean_object* v_u_1632_ = _args[2];
lean_object* v_v_1633_ = _args[3];
lean_object* v_k_1634_ = _args[4];
lean_object* v_k_x27_1635_ = _args[5];
lean_object* v_a_1636_ = _args[6];
lean_object* v_a_1637_ = _args[7];
lean_object* v_a_1638_ = _args[8];
lean_object* v_a_1639_ = _args[9];
lean_object* v_a_1640_ = _args[10];
lean_object* v_a_1641_ = _args[11];
lean_object* v_a_1642_ = _args[12];
lean_object* v_a_1643_ = _args[13];
lean_object* v_a_1644_ = _args[14];
lean_object* v_a_1645_ = _args[15];
lean_object* v_a_1646_ = _args[16];
lean_object* v_a_1647_ = _args[17];
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1630_, v_e_1631_, v_u_1632_, v_v_1633_, v_k_1634_, v_k_x27_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1642_);
lean_dec_ref(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_k_x27_1635_);
lean_dec_ref(v_k_1634_);
lean_dec(v_v_1633_);
lean_dec(v_u_1632_);
return v_res_1648_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1650_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1651_ = lean_unsigned_to_nat(2u);
v___x_1652_ = lean_unsigned_to_nat(111u);
v___x_1653_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1654_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1655_ = l_mkPanicMessageWithDecl(v___x_1654_, v___x_1653_, v___x_1652_, v___x_1651_, v___x_1650_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1656_, lean_object* v_e_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_u_1670_; lean_object* v_v_1671_; lean_object* v_e_1672_; lean_object* v_h_x3f_1673_; lean_object* v___x_1674_; 
v_u_1670_ = lean_ctor_get(v_c_1656_, 0);
v_v_1671_ = lean_ctor_get(v_c_1656_, 1);
v_e_1672_ = lean_ctor_get(v_c_1656_, 3);
lean_inc_ref(v_e_1672_);
v_h_x3f_1673_ = lean_ctor_get(v_c_1656_, 4);
lean_inc(v_h_x3f_1673_);
v___x_1674_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1670_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; uint8_t v___x_1676_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref(v___x_1674_);
v___x_1676_ = lean_nat_dec_eq(v_u_1670_, v_v_1671_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v_a_1675_);
lean_dec(v_h_x3f_1673_);
lean_dec_ref(v_e_1672_);
lean_dec_ref(v_e_1657_);
lean_dec_ref(v_c_1656_);
v___x_1677_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1678_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1677_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
return v___x_1678_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1656_);
lean_dec_ref(v_c_1656_);
lean_inc(v_a_1668_);
lean_inc_ref(v_a_1667_);
lean_inc(v_a_1666_);
lean_inc_ref(v_a_1665_);
lean_inc_ref(v_a_1663_);
lean_inc_ref(v_a_1661_);
lean_inc(v_a_1659_);
v___x_1680_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1675_, v___x_1679_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec_ref(v___x_1679_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v_h_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
if (lean_obj_tag(v_h_x3f_1673_) == 1)
{
lean_object* v_val_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v_val_1710_ = lean_ctor_get(v_h_x3f_1673_, 0);
lean_inc(v_val_1710_);
lean_dec_ref(v_h_x3f_1673_);
v___x_1711_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1657_);
v___x_1712_ = l_Lean_mkApp4(v___x_1711_, v_e_1657_, v_e_1672_, v_val_1710_, v_a_1681_);
v_h_1683_ = v___x_1712_;
v___y_1684_ = v_a_1659_;
v___y_1685_ = v_a_1661_;
v___y_1686_ = v_a_1663_;
v___y_1687_ = v_a_1665_;
v___y_1688_ = v_a_1666_;
v___y_1689_ = v_a_1667_;
v___y_1690_ = v_a_1668_;
goto v___jp_1682_;
}
else
{
lean_dec(v_h_x3f_1673_);
lean_dec_ref(v_e_1672_);
v_h_1683_ = v_a_1681_;
v___y_1684_ = v_a_1659_;
v___y_1685_ = v_a_1661_;
v___y_1686_ = v_a_1663_;
v___y_1687_ = v_a_1665_;
v___y_1688_ = v_a_1666_;
v___y_1689_ = v_a_1667_;
v___y_1690_ = v_a_1668_;
goto v___jp_1682_;
}
v___jp_1682_:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1684_, v___y_1689_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v_termMapInv_1693_; lean_object* v___x_1694_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
lean_inc(v_a_1692_);
lean_dec_ref(v___x_1691_);
v_termMapInv_1693_ = lean_ctor_get(v_a_1692_, 4);
lean_inc_ref(v_termMapInv_1693_);
lean_dec(v_a_1692_);
v___x_1694_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1693_, v_e_1657_);
if (lean_obj_tag(v___x_1694_) == 1)
{
lean_object* v_val_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_val_1695_);
lean_dec_ref(v___x_1694_);
v_fst_1696_ = lean_ctor_get(v_val_1695_, 0);
lean_inc(v_fst_1696_);
v_snd_1697_ = lean_ctor_get(v_val_1695_, 1);
lean_inc(v_snd_1697_);
lean_dec(v_val_1695_);
v___x_1698_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc(v_fst_1696_);
v___x_1699_ = l_Lean_mkApp4(v___x_1698_, v_fst_1696_, v_e_1657_, v_snd_1697_, v_h_1683_);
v___x_1700_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1696_, v___x_1699_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
return v___x_1700_;
}
else
{
lean_object* v___x_1701_; 
lean_dec(v___x_1694_);
v___x_1701_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1657_, v_h_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
return v___x_1701_;
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v_h_1683_);
lean_dec_ref(v_e_1657_);
v_a_1702_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1691_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1691_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec(v_h_x3f_1673_);
lean_dec_ref(v_e_1672_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec_ref(v_a_1663_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1659_);
lean_dec_ref(v_e_1657_);
v_a_1713_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1680_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1680_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_h_x3f_1673_);
lean_dec_ref(v_e_1672_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_e_1657_);
lean_dec_ref(v_c_1656_);
v_a_1721_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1674_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1674_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1729_, lean_object* v_e_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1729_, v_e_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1745_, v_a_1746_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1758_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1758_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_termMapInv_1753_; lean_object* v___x_1754_; lean_object* v___x_1756_; 
v_termMapInv_1753_ = lean_ctor_get(v_a_1749_, 4);
lean_inc_ref(v_termMapInv_1753_);
lean_dec(v_a_1749_);
v___x_1754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1753_, v_e_1744_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1748_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1748_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1767_, v_a_1768_, v_a_1769_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_e_1767_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1772_, v_a_1773_, v_a_1781_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_res_1797_; 
v_res_1797_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
lean_dec(v_a_1789_);
lean_dec_ref(v_a_1788_);
lean_dec(v_a_1787_);
lean_dec(v_a_1786_);
lean_dec_ref(v_e_1785_);
return v_res_1797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1798_){
_start:
{
lean_object* v_id_1799_; lean_object* v_type_1800_; lean_object* v_u_1801_; lean_object* v_isPreorderInst_1802_; lean_object* v_leInst_1803_; lean_object* v_ltInst_x3f_1804_; lean_object* v_isPartialInst_x3f_1805_; lean_object* v_isLinearPreInst_x3f_1806_; lean_object* v_lawfulOrderLTInst_x3f_1807_; lean_object* v_ringId_x3f_1808_; uint8_t v_isCommRing_1809_; lean_object* v_ringInst_x3f_1810_; lean_object* v_orderedRingInst_x3f_1811_; lean_object* v_leFn_1812_; lean_object* v_ltFn_x3f_1813_; lean_object* v_nodes_1814_; lean_object* v_nodeMap_1815_; lean_object* v_cnstrs_1816_; lean_object* v_cnstrsOf_1817_; lean_object* v_sources_1818_; lean_object* v_targets_1819_; lean_object* v_proofs_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_id_1799_ = lean_ctor_get(v_s_1798_, 0);
v_type_1800_ = lean_ctor_get(v_s_1798_, 1);
v_u_1801_ = lean_ctor_get(v_s_1798_, 2);
v_isPreorderInst_1802_ = lean_ctor_get(v_s_1798_, 3);
v_leInst_1803_ = lean_ctor_get(v_s_1798_, 4);
v_ltInst_x3f_1804_ = lean_ctor_get(v_s_1798_, 5);
v_isPartialInst_x3f_1805_ = lean_ctor_get(v_s_1798_, 6);
v_isLinearPreInst_x3f_1806_ = lean_ctor_get(v_s_1798_, 7);
v_lawfulOrderLTInst_x3f_1807_ = lean_ctor_get(v_s_1798_, 8);
v_ringId_x3f_1808_ = lean_ctor_get(v_s_1798_, 9);
v_isCommRing_1809_ = lean_ctor_get_uint8(v_s_1798_, sizeof(void*)*22);
v_ringInst_x3f_1810_ = lean_ctor_get(v_s_1798_, 10);
v_orderedRingInst_x3f_1811_ = lean_ctor_get(v_s_1798_, 11);
v_leFn_1812_ = lean_ctor_get(v_s_1798_, 12);
v_ltFn_x3f_1813_ = lean_ctor_get(v_s_1798_, 13);
v_nodes_1814_ = lean_ctor_get(v_s_1798_, 14);
v_nodeMap_1815_ = lean_ctor_get(v_s_1798_, 15);
v_cnstrs_1816_ = lean_ctor_get(v_s_1798_, 16);
v_cnstrsOf_1817_ = lean_ctor_get(v_s_1798_, 17);
v_sources_1818_ = lean_ctor_get(v_s_1798_, 18);
v_targets_1819_ = lean_ctor_get(v_s_1798_, 19);
v_proofs_1820_ = lean_ctor_get(v_s_1798_, 20);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_s_1798_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_s_1798_, 21);
lean_dec(v_unused_1829_);
v___x_1822_ = v_s_1798_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_proofs_1820_);
lean_inc(v_targets_1819_);
lean_inc(v_sources_1818_);
lean_inc(v_cnstrsOf_1817_);
lean_inc(v_cnstrs_1816_);
lean_inc(v_nodeMap_1815_);
lean_inc(v_nodes_1814_);
lean_inc(v_ltFn_x3f_1813_);
lean_inc(v_leFn_1812_);
lean_inc(v_orderedRingInst_x3f_1811_);
lean_inc(v_ringInst_x3f_1810_);
lean_inc(v_ringId_x3f_1808_);
lean_inc(v_lawfulOrderLTInst_x3f_1807_);
lean_inc(v_isLinearPreInst_x3f_1806_);
lean_inc(v_isPartialInst_x3f_1805_);
lean_inc(v_ltInst_x3f_1804_);
lean_inc(v_leInst_1803_);
lean_inc(v_isPreorderInst_1802_);
lean_inc(v_u_1801_);
lean_inc(v_type_1800_);
lean_inc(v_id_1799_);
lean_dec(v_s_1798_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 21, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_id_1799_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_type_1800_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_u_1801_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_isPreorderInst_1802_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_leInst_1803_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_ltInst_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_isPartialInst_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_isLinearPreInst_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_lawfulOrderLTInst_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 9, v_ringId_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 10, v_ringInst_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1827_, 11, v_orderedRingInst_x3f_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 12, v_leFn_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 13, v_ltFn_x3f_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 14, v_nodes_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 15, v_nodeMap_1815_);
lean_ctor_set(v_reuseFailAlloc_1827_, 16, v_cnstrs_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 17, v_cnstrsOf_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 18, v_sources_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 19, v_targets_1819_);
lean_ctor_set(v_reuseFailAlloc_1827_, 20, v_proofs_1820_);
lean_ctor_set(v_reuseFailAlloc_1827_, 21, v___x_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*22, v_isCommRing_1809_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_box(0);
v___x_1837_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1838_ = l_Lean_mkConst(v___x_1837_, v___x_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1839_, lean_object* v_b_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
if (lean_obj_tag(v_as_x27_1839_) == 0)
{
lean_object* v___x_1853_; 
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_b_1840_);
return v___x_1853_;
}
else
{
lean_object* v_head_1854_; lean_object* v_tail_1855_; lean_object* v___x_1856_; 
v_head_1854_ = lean_ctor_get(v_as_x27_1839_, 0);
lean_inc(v_head_1854_);
v_tail_1855_ = lean_ctor_get(v_as_x27_1839_, 1);
lean_inc(v_tail_1855_);
lean_dec_ref(v_as_x27_1839_);
v___x_1856_ = lean_box(0);
switch(lean_obj_tag(v_head_1854_))
{
case 0:
{
lean_object* v_c_1857_; lean_object* v_e_1858_; lean_object* v_u_1859_; lean_object* v_v_1860_; lean_object* v_k_1861_; lean_object* v_k_x27_1862_; lean_object* v___x_1863_; 
v_c_1857_ = lean_ctor_get(v_head_1854_, 0);
lean_inc_ref(v_c_1857_);
v_e_1858_ = lean_ctor_get(v_head_1854_, 1);
lean_inc_ref(v_e_1858_);
v_u_1859_ = lean_ctor_get(v_head_1854_, 2);
lean_inc(v_u_1859_);
v_v_1860_ = lean_ctor_get(v_head_1854_, 3);
lean_inc(v_v_1860_);
v_k_1861_ = lean_ctor_get(v_head_1854_, 4);
lean_inc_ref(v_k_1861_);
v_k_x27_1862_ = lean_ctor_get(v_head_1854_, 5);
lean_inc_ref(v_k_x27_1862_);
lean_dec_ref(v_head_1854_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc(v___y_1841_);
v___x_1863_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1857_, v_e_1858_, v_u_1859_, v_v_1860_, v_k_1861_, v_k_x27_1862_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v_k_x27_1862_);
lean_dec_ref(v_k_1861_);
lean_dec(v_v_1860_);
lean_dec(v_u_1859_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_dec_ref(v___x_1863_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
else
{
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
return v___x_1863_;
}
}
case 1:
{
lean_object* v_c_1865_; lean_object* v_e_1866_; lean_object* v_u_1867_; lean_object* v_v_1868_; lean_object* v_k_1869_; lean_object* v_k_x27_1870_; lean_object* v___x_1871_; 
v_c_1865_ = lean_ctor_get(v_head_1854_, 0);
lean_inc_ref(v_c_1865_);
v_e_1866_ = lean_ctor_get(v_head_1854_, 1);
lean_inc_ref(v_e_1866_);
v_u_1867_ = lean_ctor_get(v_head_1854_, 2);
lean_inc(v_u_1867_);
v_v_1868_ = lean_ctor_get(v_head_1854_, 3);
lean_inc(v_v_1868_);
v_k_1869_ = lean_ctor_get(v_head_1854_, 4);
lean_inc_ref(v_k_1869_);
v_k_x27_1870_ = lean_ctor_get(v_head_1854_, 5);
lean_inc_ref(v_k_x27_1870_);
lean_dec_ref(v_head_1854_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
v___x_1871_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1865_, v_e_1866_, v_u_1867_, v_v_1868_, v_k_1869_, v_k_x27_1870_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec_ref(v_k_x27_1870_);
lean_dec_ref(v_k_1869_);
lean_dec(v_v_1868_);
lean_dec(v_u_1867_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_dec_ref(v___x_1871_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
else
{
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
return v___x_1871_;
}
}
default: 
{
lean_object* v_u_1873_; lean_object* v_v_1874_; lean_object* v___x_1875_; 
v_u_1873_ = lean_ctor_get(v_head_1854_, 0);
lean_inc(v_u_1873_);
v_v_1874_ = lean_ctor_get(v_head_1854_, 1);
lean_inc(v_v_1874_);
lean_dec_ref(v_head_1854_);
v___x_1875_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1873_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1877_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref(v___x_1875_);
v___x_1877_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1874_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1999_; lean_object* v___x_2053_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_2053_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1876_, v___y_1842_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; uint8_t v___x_2055_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
v___x_2055_ = lean_unbox(v_a_2054_);
lean_dec(v_a_2054_);
if (v___x_2055_ == 0)
{
v___y_1999_ = v___x_2053_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2056_; 
lean_dec_ref(v___x_2053_);
v___x_2056_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1878_, v___y_1842_);
v___y_1999_ = v___x_2056_;
goto v___jp_1998_;
}
}
else
{
v___y_1999_ = v___x_2053_;
goto v___jp_1998_;
}
v___jp_1879_:
{
if (lean_obj_tag(v___y_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___y_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___y_1895_);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1887_, v___y_1894_, v___y_1881_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; uint8_t v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v___x_1901_ = lean_unbox(v_a_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1873_, v_v_1874_, v___y_1893_, v___y_1881_, v___y_1880_, v___y_1886_, v___y_1883_, v___y_1885_, v___y_1889_, v___y_1890_, v___y_1892_, v___y_1884_, v___y_1882_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1874_, v_u_1873_, v___y_1893_, v___y_1881_, v___y_1880_, v___y_1886_, v___y_1883_, v___y_1885_, v___y_1889_, v___y_1890_, v___y_1892_, v___y_1884_, v___y_1882_);
lean_dec(v_u_1873_);
lean_dec(v_v_1874_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref(v___x_1904_);
lean_inc(v_a_1878_);
lean_inc(v_a_1876_);
v___x_1906_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1876_, v_a_1878_, v_a_1903_, v_a_1905_, v___y_1893_, v___y_1881_, v___y_1880_, v___y_1886_, v___y_1883_, v___y_1885_, v___y_1889_, v___y_1890_, v___y_1892_, v___y_1884_, v___y_1882_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1883_);
lean_dec(v___y_1880_);
lean_dec(v___y_1893_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref(v___x_1906_);
v___x_1908_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1894_);
lean_inc_ref(v___y_1887_);
v___x_1909_ = l_Lean_mkApp7(v___x_1908_, v___y_1887_, v___y_1894_, v_a_1876_, v_a_1878_, v___y_1888_, v___y_1891_, v_a_1907_);
v___x_1910_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
v___x_1911_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1887_, v___y_1894_, v___x_1909_, v___x_1910_, v___y_1881_, v___y_1886_, v___y_1890_, v___y_1892_, v___y_1884_, v___y_1882_);
lean_dec_ref(v___y_1886_);
lean_dec(v___y_1881_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_dec_ref(v___x_1911_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
else
{
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
return v___x_1911_;
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1900_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1913_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1906_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1906_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1903_);
lean_dec(v_a_1900_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1921_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1904_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1904_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec(v_a_1900_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1929_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1902_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1902_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
else
{
lean_dec(v_a_1900_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1938_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1899_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1899_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1884_);
lean_dec(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1946_ = lean_ctor_get(v___y_1895_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___y_1895_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___y_1895_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___y_1895_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
v___jp_1954_:
{
lean_object* v___x_1966_; 
v___x_1966_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1876_, v___y_1956_, v___y_1964_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1966_);
if (lean_obj_tag(v_a_1967_) == 1)
{
lean_object* v_val_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1971_; 
v_val_1968_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_a_1967_);
v_fst_1969_ = lean_ctor_get(v_val_1968_, 0);
lean_inc(v_fst_1969_);
v_snd_1970_ = lean_ctor_get(v_val_1968_, 1);
lean_inc(v_snd_1970_);
lean_dec(v_val_1968_);
v___x_1971_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1878_, v___y_1956_, v___y_1964_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
if (lean_obj_tag(v_a_1972_) == 1)
{
lean_object* v_val_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1976_; 
v_val_1973_ = lean_ctor_get(v_a_1972_, 0);
lean_inc(v_val_1973_);
lean_dec_ref(v_a_1972_);
v_fst_1974_ = lean_ctor_get(v_val_1973_, 0);
lean_inc(v_fst_1974_);
v_snd_1975_ = lean_ctor_get(v_val_1973_, 1);
lean_inc(v_snd_1975_);
lean_dec(v_val_1973_);
v___x_1976_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1969_, v___y_1956_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; uint8_t v___x_1978_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
v___x_1978_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_1978_ == 0)
{
v___y_1880_ = v___y_1957_;
v___y_1881_ = v___y_1956_;
v___y_1882_ = v___y_1965_;
v___y_1883_ = v___y_1959_;
v___y_1884_ = v___y_1964_;
v___y_1885_ = v___y_1960_;
v___y_1886_ = v___y_1958_;
v___y_1887_ = v_fst_1969_;
v___y_1888_ = v_snd_1970_;
v___y_1889_ = v___y_1961_;
v___y_1890_ = v___y_1962_;
v___y_1891_ = v_snd_1975_;
v___y_1892_ = v___y_1963_;
v___y_1893_ = v___y_1955_;
v___y_1894_ = v_fst_1974_;
v___y_1895_ = v___x_1976_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1979_; 
lean_dec_ref(v___x_1976_);
v___x_1979_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1974_, v___y_1956_);
v___y_1880_ = v___y_1957_;
v___y_1881_ = v___y_1956_;
v___y_1882_ = v___y_1965_;
v___y_1883_ = v___y_1959_;
v___y_1884_ = v___y_1964_;
v___y_1885_ = v___y_1960_;
v___y_1886_ = v___y_1958_;
v___y_1887_ = v_fst_1969_;
v___y_1888_ = v_snd_1970_;
v___y_1889_ = v___y_1961_;
v___y_1890_ = v___y_1962_;
v___y_1891_ = v_snd_1975_;
v___y_1892_ = v___y_1963_;
v___y_1893_ = v___y_1955_;
v___y_1894_ = v_fst_1974_;
v___y_1895_ = v___x_1979_;
goto v___jp_1879_;
}
}
else
{
v___y_1880_ = v___y_1957_;
v___y_1881_ = v___y_1956_;
v___y_1882_ = v___y_1965_;
v___y_1883_ = v___y_1959_;
v___y_1884_ = v___y_1964_;
v___y_1885_ = v___y_1960_;
v___y_1886_ = v___y_1958_;
v___y_1887_ = v_fst_1969_;
v___y_1888_ = v_snd_1970_;
v___y_1889_ = v___y_1961_;
v___y_1890_ = v___y_1962_;
v___y_1891_ = v_snd_1975_;
v___y_1892_ = v___y_1963_;
v___y_1893_ = v___y_1955_;
v___y_1894_ = v_fst_1974_;
v___y_1895_ = v___x_1976_;
goto v___jp_1879_;
}
}
else
{
lean_dec(v_a_1972_);
lean_dec(v_snd_1970_);
lean_dec(v_fst_1969_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec(v_snd_1970_);
lean_dec(v_fst_1969_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1981_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1971_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1971_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
else
{
lean_dec(v_a_1967_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
v_as_x27_1839_ = v_tail_1855_;
v_b_1840_ = v___x_1856_;
goto _start;
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_1990_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1966_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1966_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
v___jp_1998_:
{
if (lean_obj_tag(v___y_1999_) == 0)
{
lean_object* v_a_2000_; uint8_t v___x_2001_; 
v_a_2000_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___y_1999_);
v___x_2001_ = lean_unbox(v_a_2000_);
lean_dec(v_a_2000_);
if (v___x_2001_ == 0)
{
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc(v___y_1841_);
v___y_1955_ = v___y_1841_;
v___y_1956_ = v___y_1842_;
v___y_1957_ = v___y_1843_;
v___y_1958_ = v___y_1844_;
v___y_1959_ = v___y_1845_;
v___y_1960_ = v___y_1846_;
v___y_1961_ = v___y_1847_;
v___y_1962_ = v___y_1848_;
v___y_1963_ = v___y_1849_;
v___y_1964_ = v___y_1850_;
v___y_1965_ = v___y_1851_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1876_, v_a_1878_, v___y_1842_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; uint8_t v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
v___x_2004_ = lean_unbox(v_a_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
v___x_2005_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1873_, v_v_1874_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1874_, v_u_1873_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
lean_inc(v_a_1878_);
lean_inc(v_a_1876_);
v___x_2009_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1876_, v_a_1878_, v_a_2006_, v_a_2008_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; lean_object* v___x_2012_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_2009_);
v___x_2011_ = lean_unbox(v_a_2003_);
lean_dec(v_a_2003_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v_a_1878_);
lean_inc(v_a_1876_);
v___x_2012_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1876_, v_a_1878_, v_a_2010_, v___x_2011_, v___y_1842_, v___y_1844_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_dec_ref(v___x_2012_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc(v___y_1841_);
v___y_1955_ = v___y_1841_;
v___y_1956_ = v___y_1842_;
v___y_1957_ = v___y_1843_;
v___y_1958_ = v___y_1844_;
v___y_1959_ = v___y_1845_;
v___y_1960_ = v___y_1846_;
v___y_1961_ = v___y_1847_;
v___y_1962_ = v___y_1848_;
v___y_1963_ = v___y_1849_;
v___y_1964_ = v___y_1850_;
v___y_1965_ = v___y_1851_;
goto v___jp_1954_;
}
else
{
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
return v___x_2012_;
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_a_2003_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2013_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2009_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_a_2006_);
lean_dec(v_a_2003_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2021_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2007_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2007_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_a_2003_);
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2029_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2005_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2005_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_dec(v_a_2003_);
lean_inc(v___y_1851_);
lean_inc_ref(v___y_1850_);
lean_inc(v___y_1849_);
lean_inc_ref(v___y_1848_);
lean_inc(v___y_1847_);
lean_inc_ref(v___y_1846_);
lean_inc(v___y_1845_);
lean_inc_ref(v___y_1844_);
lean_inc(v___y_1843_);
lean_inc(v___y_1842_);
lean_inc(v___y_1841_);
v___y_1955_ = v___y_1841_;
v___y_1956_ = v___y_1842_;
v___y_1957_ = v___y_1843_;
v___y_1958_ = v___y_1844_;
v___y_1959_ = v___y_1845_;
v___y_1960_ = v___y_1846_;
v___y_1961_ = v___y_1847_;
v___y_1962_ = v___y_1848_;
v___y_1963_ = v___y_1849_;
v___y_1964_ = v___y_1850_;
v___y_1965_ = v___y_1851_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2037_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2002_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2002_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_1878_);
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2045_ = lean_ctor_get(v___y_1999_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___y_1999_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___y_1999_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_1876_);
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2057_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1877_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1877_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec(v_v_1874_);
lean_dec(v_u_1873_);
lean_dec(v_tail_1855_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec(v___y_1841_);
v_a_2065_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_1875_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_1875_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2073_, v_b_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v___f_2103_; lean_object* v___x_2104_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v___f_2103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
lean_inc(v_a_2089_);
v___x_2104_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_2103_, v_a_2089_, v_a_2090_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_propagate_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec_ref(v___x_2104_);
v_propagate_2105_ = lean_ctor_get(v_a_2102_, 21);
lean_inc(v_propagate_2105_);
lean_dec(v_a_2102_);
v___x_2106_ = lean_box(0);
v___x_2107_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_2105_, v___x_2106_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v___x_2107_, 0);
lean_dec(v_unused_2115_);
v___x_2109_ = v___x_2107_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v___x_2107_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2106_);
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2106_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
return v___x_2107_;
}
}
else
{
lean_dec(v_a_2102_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec(v_a_2089_);
return v___x_2104_;
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec(v_a_2090_);
lean_dec(v_a_2089_);
v_a_2116_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2101_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2101_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2137_, lean_object* v_as_x27_2138_, lean_object* v_b_2139_, lean_object* v_a_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2138_, v_b_2139_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2154_, lean_object* v_as_x27_2155_, lean_object* v_b_2156_, lean_object* v_a_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2154_, v_as_x27_2155_, v_b_2156_, v_a_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
lean_dec(v_as_2154_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2172_, v_a_2176_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v_termMapInv_2181_; lean_object* v___x_2182_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
v_termMapInv_2181_ = lean_ctor_get(v_a_2180_, 4);
lean_inc_ref(v_termMapInv_2181_);
lean_dec(v_a_2180_);
v___x_2182_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2181_, v_e_2171_);
if (lean_obj_tag(v___x_2182_) == 1)
{
lean_object* v_val_2183_; lean_object* v_fst_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v_e_2171_);
v_val_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_val_2183_);
lean_dec_ref(v___x_2182_);
v_fst_2184_ = lean_ctor_get(v_val_2183_, 0);
lean_inc(v_fst_2184_);
lean_dec(v_val_2183_);
v___x_2185_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2184_, v_a_2172_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; uint8_t v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
v___x_2187_ = lean_unbox(v_a_2186_);
lean_dec(v_a_2186_);
if (v___x_2187_ == 0)
{
lean_dec(v_fst_2184_);
return v___x_2185_;
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v___x_2185_);
v___x_2188_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2184_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2188_;
}
}
else
{
lean_dec(v_fst_2184_);
return v___x_2185_;
}
}
else
{
lean_object* v___x_2189_; 
lean_dec(v___x_2182_);
v___x_2189_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2171_, v_a_2172_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; uint8_t v___x_2191_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
v___x_2191_ = lean_unbox(v_a_2190_);
lean_dec(v_a_2190_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v_e_2171_);
return v___x_2189_;
}
else
{
lean_object* v___x_2192_; 
lean_dec_ref(v___x_2189_);
v___x_2192_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2192_;
}
}
else
{
lean_dec_ref(v_e_2171_);
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec_ref(v_e_2171_);
v_a_2193_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2179_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2179_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
lean_dec(v_a_2207_);
lean_dec_ref(v_a_2206_);
lean_dec(v_a_2205_);
lean_dec_ref(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2210_, v_a_2212_, v_a_2216_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2));
v___x_2246_ = l_Lean_stringToMessageData(v___x_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2248_, lean_object* v_v_2249_, lean_object* v_k_2250_, lean_object* v_c_2251_, lean_object* v_e_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v___x_2265_; 
lean_inc_ref(v_e_2252_);
v___x_2265_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2252_, v_a_2254_, v_a_2258_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2366_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2366_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2366_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_unbox(v_a_2266_);
lean_dec(v_a_2266_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2361_; 
lean_del_object(v___x_2268_);
v___x_2271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2272_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2271_, v_a_2262_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2361_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2361_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; uint8_t v___x_2297_; 
v___x_2277_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2251_);
v___x_2297_ = lean_unbox(v_a_2273_);
lean_dec(v_a_2273_);
if (v___x_2297_ == 0)
{
v___y_2279_ = v_a_2253_;
v___y_2280_ = v_a_2254_;
v___y_2281_ = v_a_2255_;
v___y_2282_ = v_a_2256_;
v___y_2283_ = v_a_2257_;
v___y_2284_ = v_a_2258_;
v___y_2285_ = v_a_2259_;
v___y_2286_ = v_a_2260_;
v___y_2287_ = v_a_2261_;
v___y_2288_ = v_a_2262_;
v___y_2289_ = v_a_2263_;
goto v___jp_2278_;
}
else
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2248_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2249_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2251_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_k_2304_; uint8_t v_strict_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___y_2322_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v_k_2304_ = lean_ctor_get(v_k_2250_, 0);
v_strict_2305_ = lean_ctor_get_uint8(v_k_2250_, sizeof(void*)*1);
v___x_2306_ = l_Lean_MessageData_ofExpr(v_a_2299_);
v___x_2307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2306_);
lean_ctor_set(v___x_2317_, 1, v___x_2307_);
v___x_2318_ = l_Lean_MessageData_ofExpr(v_a_2301_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___x_2307_);
if (v_strict_2305_ == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Int_repr(v_k_2304_);
v___y_2322_ = v___x_2333_;
goto v___jp_2321_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = l_Int_repr(v_k_2304_);
v___x_2335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
v___x_2336_ = lean_string_append(v___x_2334_, v___x_2335_);
v___y_2322_ = v___x_2336_;
goto v___jp_2321_;
}
v___jp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___y_2310_);
v___x_2312_ = l_Lean_MessageData_ofFormat(v___x_2311_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___y_2309_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2307_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v_a_2303_);
v___x_2316_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v___x_2271_, v___x_2315_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_dec_ref(v___x_2316_);
v___y_2279_ = v_a_2253_;
v___y_2280_ = v_a_2254_;
v___y_2281_ = v_a_2255_;
v___y_2282_ = v_a_2256_;
v___y_2283_ = v_a_2257_;
v___y_2284_ = v_a_2258_;
v___y_2285_ = v_a_2259_;
v___y_2286_ = v_a_2260_;
v___y_2287_ = v_a_2261_;
v___y_2288_ = v_a_2262_;
v___y_2289_ = v_a_2263_;
goto v___jp_2278_;
}
else
{
lean_dec_ref(v___x_2277_);
lean_del_object(v___x_2275_);
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
return v___x_2316_;
}
}
v___jp_2321_:
{
lean_object* v_k_2323_; uint8_t v_strict_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_k_2323_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_k_2323_);
v_strict_2324_ = lean_ctor_get_uint8(v___x_2277_, sizeof(void*)*1);
v___x_2325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___y_2322_);
v___x_2326_ = l_Lean_MessageData_ofFormat(v___x_2325_);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2320_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2307_);
if (v_strict_2324_ == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Int_repr(v_k_2323_);
lean_dec(v_k_2323_);
v___y_2309_ = v___x_2328_;
v___y_2310_ = v___x_2329_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = l_Int_repr(v_k_2323_);
lean_dec(v_k_2323_);
v___x_2331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
v___x_2332_ = lean_string_append(v___x_2330_, v___x_2331_);
v___y_2309_ = v___x_2328_;
v___y_2310_ = v___x_2332_;
goto v___jp_2308_;
}
}
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_a_2301_);
lean_dec(v_a_2299_);
lean_dec_ref(v___x_2277_);
lean_del_object(v___x_2275_);
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v_a_2337_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2302_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2302_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_a_2299_);
lean_dec_ref(v___x_2277_);
lean_del_object(v___x_2275_);
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v_a_2345_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2300_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2300_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___x_2277_);
lean_del_object(v___x_2275_);
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v_a_2353_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2298_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2298_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
v___jp_2278_:
{
uint8_t v___x_2290_; 
v___x_2290_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2250_, v___x_2277_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
lean_dec(v___y_2279_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v___x_2291_ = lean_box(0);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2291_);
v___x_2293_ = v___x_2275_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_del_object(v___x_2275_);
v___x_2295_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2295_, 0, v_c_2251_);
lean_ctor_set(v___x_2295_, 1, v_e_2252_);
lean_ctor_set(v___x_2295_, 2, v_u_2248_);
lean_ctor_set(v___x_2295_, 3, v_v_2249_);
lean_ctor_set(v___x_2295_, 4, v_k_2250_);
lean_ctor_set(v___x_2295_, 5, v___x_2277_);
v___x_2296_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2295_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2296_;
}
}
}
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v___x_2362_ = lean_box(0);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2362_);
v___x_2364_ = v___x_2268_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec(v_a_2253_);
lean_dec_ref(v_e_2252_);
lean_dec_ref(v_c_2251_);
lean_dec_ref(v_k_2250_);
lean_dec(v_v_2249_);
lean_dec(v_u_2248_);
v_a_2367_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2265_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2265_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2375_ = _args[0];
lean_object* v_v_2376_ = _args[1];
lean_object* v_k_2377_ = _args[2];
lean_object* v_c_2378_ = _args[3];
lean_object* v_e_2379_ = _args[4];
lean_object* v_a_2380_ = _args[5];
lean_object* v_a_2381_ = _args[6];
lean_object* v_a_2382_ = _args[7];
lean_object* v_a_2383_ = _args[8];
lean_object* v_a_2384_ = _args[9];
lean_object* v_a_2385_ = _args[10];
lean_object* v_a_2386_ = _args[11];
lean_object* v_a_2387_ = _args[12];
lean_object* v_a_2388_ = _args[13];
lean_object* v_a_2389_ = _args[14];
lean_object* v_a_2390_ = _args[15];
lean_object* v_a_2391_ = _args[16];
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2375_, v_v_2376_, v_k_2377_, v_c_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec(v_a_2381_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2394_, v_a_2398_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v_termMapInv_2403_; lean_object* v___x_2404_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
lean_inc(v_a_2402_);
lean_dec_ref(v___x_2401_);
v_termMapInv_2403_ = lean_ctor_get(v_a_2402_, 4);
lean_inc_ref(v_termMapInv_2403_);
lean_dec(v_a_2402_);
v___x_2404_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2403_, v_e_2393_);
if (lean_obj_tag(v___x_2404_) == 1)
{
lean_object* v_val_2405_; lean_object* v_fst_2406_; lean_object* v___x_2407_; 
lean_dec_ref(v_e_2393_);
v_val_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_val_2405_);
lean_dec_ref(v___x_2404_);
v_fst_2406_ = lean_ctor_get(v_val_2405_, 0);
lean_inc(v_fst_2406_);
lean_dec(v_val_2405_);
v___x_2407_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2406_, v_a_2394_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; uint8_t v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
v___x_2409_ = lean_unbox(v_a_2408_);
lean_dec(v_a_2408_);
if (v___x_2409_ == 0)
{
lean_dec(v_fst_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2410_; 
lean_dec_ref(v___x_2407_);
v___x_2410_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2406_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2410_;
}
}
else
{
lean_dec(v_fst_2406_);
return v___x_2407_;
}
}
else
{
lean_object* v___x_2411_; 
lean_dec(v___x_2404_);
v___x_2411_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2393_, v_a_2394_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; uint8_t v___x_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
v___x_2413_ = lean_unbox(v_a_2412_);
lean_dec(v_a_2412_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_e_2393_);
return v___x_2411_;
}
else
{
lean_object* v___x_2414_; 
lean_dec_ref(v___x_2411_);
v___x_2414_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_);
return v___x_2414_;
}
}
else
{
lean_dec_ref(v_e_2393_);
return v___x_2411_;
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec_ref(v_e_2393_);
v_a_2415_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2401_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2401_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2432_, v_a_2434_, v_a_2438_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2446_, v_a_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_);
lean_dec(v_a_2457_);
lean_dec_ref(v_a_2456_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec(v_a_2448_);
lean_dec(v_a_2447_);
return v_res_2459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2469_, lean_object* v_v_2470_, lean_object* v_k_2471_, lean_object* v_c_2472_, lean_object* v_e_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_){
_start:
{
lean_object* v___x_2486_; 
lean_inc_ref(v_e_2473_);
v___x_2486_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2473_, v_a_2475_, v_a_2479_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2589_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2489_ = v___x_2486_;
v_isShared_2490_ = v_isSharedCheck_2589_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2486_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2589_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_unbox(v_a_2487_);
lean_dec(v_a_2487_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2584_; 
lean_del_object(v___x_2489_);
v___x_2492_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2493_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2492_, v_a_2483_);
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2496_ = v___x_2493_;
v_isShared_2497_ = v_isSharedCheck_2584_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2493_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2584_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; uint8_t v___x_2519_; 
v___x_2498_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2472_);
v___x_2519_ = lean_unbox(v_a_2494_);
lean_dec(v_a_2494_);
if (v___x_2519_ == 0)
{
v___y_2500_ = v_a_2474_;
v___y_2501_ = v_a_2475_;
v___y_2502_ = v_a_2476_;
v___y_2503_ = v_a_2477_;
v___y_2504_ = v_a_2478_;
v___y_2505_ = v_a_2479_;
v___y_2506_ = v_a_2480_;
v___y_2507_ = v_a_2481_;
v___y_2508_ = v_a_2482_;
v___y_2509_ = v_a_2483_;
v___y_2510_ = v_a_2484_;
goto v___jp_2499_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2469_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2522_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_a_2521_);
lean_dec_ref(v___x_2520_);
v___x_2522_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2470_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2472_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___y_2527_; lean_object* v___y_2528_; lean_object* v_k_2536_; uint8_t v_strict_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___y_2545_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2524_);
v_k_2536_ = lean_ctor_get(v_k_2471_, 0);
v_strict_2537_ = lean_ctor_get_uint8(v_k_2471_, sizeof(void*)*1);
v___x_2538_ = l_Lean_MessageData_ofExpr(v_a_2521_);
v___x_2539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3);
v___x_2540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2538_);
lean_ctor_set(v___x_2540_, 1, v___x_2539_);
v___x_2541_ = l_Lean_MessageData_ofExpr(v_a_2523_);
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2540_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2539_);
if (v_strict_2537_ == 0)
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Int_repr(v_k_2536_);
v___y_2545_ = v___x_2556_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = l_Int_repr(v_k_2536_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
v___x_2559_ = lean_string_append(v___x_2557_, v___x_2558_);
v___y_2545_ = v___x_2559_;
goto v___jp_2544_;
}
v___jp_2526_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___y_2528_);
v___x_2530_ = l_Lean_MessageData_ofFormat(v___x_2529_);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___y_2527_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2533_);
lean_ctor_set(v___x_2534_, 1, v_a_2525_);
v___x_2535_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v___x_2492_, v___x_2534_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_dec_ref(v___x_2535_);
v___y_2500_ = v_a_2474_;
v___y_2501_ = v_a_2475_;
v___y_2502_ = v_a_2476_;
v___y_2503_ = v_a_2477_;
v___y_2504_ = v_a_2478_;
v___y_2505_ = v_a_2479_;
v___y_2506_ = v_a_2480_;
v___y_2507_ = v_a_2481_;
v___y_2508_ = v_a_2482_;
v___y_2509_ = v_a_2483_;
v___y_2510_ = v_a_2484_;
goto v___jp_2499_;
}
else
{
lean_dec_ref(v___x_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
return v___x_2535_;
}
}
v___jp_2544_:
{
lean_object* v_k_2546_; uint8_t v_strict_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_k_2546_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_k_2546_);
v_strict_2547_ = lean_ctor_get_uint8(v___x_2498_, sizeof(void*)*1);
v___x_2548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2545_);
v___x_2549_ = l_Lean_MessageData_ofFormat(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2543_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v___x_2539_);
if (v_strict_2547_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Int_repr(v_k_2546_);
lean_dec(v_k_2546_);
v___y_2527_ = v___x_2551_;
v___y_2528_ = v___x_2552_;
goto v___jp_2526_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2553_ = l_Int_repr(v_k_2546_);
lean_dec(v_k_2546_);
v___x_2554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
v___x_2555_ = lean_string_append(v___x_2553_, v___x_2554_);
v___y_2527_ = v___x_2551_;
v___y_2528_ = v___x_2555_;
goto v___jp_2526_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec(v_a_2523_);
lean_dec(v_a_2521_);
lean_dec_ref(v___x_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v_a_2560_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2524_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2524_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_a_2521_);
lean_dec_ref(v___x_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v_a_2568_ = lean_ctor_get(v___x_2522_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2522_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2522_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2522_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec_ref(v___x_2498_);
lean_del_object(v___x_2496_);
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v_a_2576_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2520_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2520_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
v___jp_2499_:
{
lean_object* v___x_2511_; uint8_t v___x_2512_; 
lean_inc_ref(v___x_2498_);
v___x_2511_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2471_, v___x_2498_);
v___x_2512_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2511_);
lean_dec_ref(v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2515_; 
lean_dec(v___y_2500_);
lean_dec_ref(v___x_2498_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v___x_2513_ = lean_box(0);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 0, v___x_2513_);
v___x_2515_ = v___x_2496_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2513_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_del_object(v___x_2496_);
v___x_2517_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2517_, 0, v_c_2472_);
lean_ctor_set(v___x_2517_, 1, v_e_2473_);
lean_ctor_set(v___x_2517_, 2, v_u_2469_);
lean_ctor_set(v___x_2517_, 3, v_v_2470_);
lean_ctor_set(v___x_2517_, 4, v_k_2471_);
lean_ctor_set(v___x_2517_, 5, v___x_2498_);
v___x_2518_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2517_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2518_;
}
}
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v___x_2585_ = lean_box(0);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 0, v___x_2585_);
v___x_2587_ = v___x_2489_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_a_2474_);
lean_dec_ref(v_e_2473_);
lean_dec_ref(v_c_2472_);
lean_dec_ref(v_k_2471_);
lean_dec(v_v_2470_);
lean_dec(v_u_2469_);
v_a_2590_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2486_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2486_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2598_ = _args[0];
lean_object* v_v_2599_ = _args[1];
lean_object* v_k_2600_ = _args[2];
lean_object* v_c_2601_ = _args[3];
lean_object* v_e_2602_ = _args[4];
lean_object* v_a_2603_ = _args[5];
lean_object* v_a_2604_ = _args[6];
lean_object* v_a_2605_ = _args[7];
lean_object* v_a_2606_ = _args[8];
lean_object* v_a_2607_ = _args[9];
lean_object* v_a_2608_ = _args[10];
lean_object* v_a_2609_ = _args[11];
lean_object* v_a_2610_ = _args[12];
lean_object* v_a_2611_ = _args[13];
lean_object* v_a_2612_ = _args[14];
lean_object* v_a_2613_ = _args[15];
lean_object* v_a_2614_ = _args[16];
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2598_, v_v_2599_, v_k_2600_, v_c_2601_, v_e_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_a_2609_);
lean_dec_ref(v_a_2608_);
lean_dec(v_a_2607_);
lean_dec_ref(v_a_2606_);
lean_dec(v_a_2605_);
lean_dec(v_a_2604_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2616_, lean_object* v_x_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v___x_2632_; 
v_fst_2630_ = lean_ctor_get(v_x_2617_, 0);
lean_inc(v_fst_2630_);
v_snd_2631_ = lean_ctor_get(v_x_2617_, 1);
lean_inc(v_snd_2631_);
lean_dec_ref(v_x_2617_);
v___x_2632_ = lean_apply_14(v_f_2616_, v_fst_2630_, v_snd_2631_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, lean_box(0));
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2633_, lean_object* v_x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2633_, v_x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v_res_2647_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1(void){
_start:
{
lean_object* v___f_2649_; lean_object* v___f_2650_; 
v___f_2649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0));
v___f_2650_ = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2650_, 0, v___f_2649_);
lean_closure_set(v___f_2650_, 1, v___f_2649_);
return v___f_2650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2651_; lean_object* v___f_2652_; 
v___x_2651_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2652_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2652_, 0, v___x_2651_);
return v___f_2652_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2653_; lean_object* v___f_2654_; 
v___f_2653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2654_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2654_, 0, v___f_2653_);
lean_closure_set(v___f_2654_, 1, v___f_2653_);
return v___f_2654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2655_, lean_object* v_v_2656_, lean_object* v_f_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
lean_object* v___x_2670_; lean_object* v_toApplicative_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2762_; 
v___x_2670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2671_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v___x_2670_, 1);
lean_dec(v_unused_2763_);
v___x_2673_ = v___x_2670_;
v_isShared_2674_ = v_isSharedCheck_2762_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_toApplicative_2671_);
lean_dec(v___x_2670_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2762_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v_toFunctor_2675_; lean_object* v_toSeq_2676_; lean_object* v_toSeqLeft_2677_; lean_object* v_toSeqRight_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2760_; 
v_toFunctor_2675_ = lean_ctor_get(v_toApplicative_2671_, 0);
v_toSeq_2676_ = lean_ctor_get(v_toApplicative_2671_, 2);
v_toSeqLeft_2677_ = lean_ctor_get(v_toApplicative_2671_, 3);
v_toSeqRight_2678_ = lean_ctor_get(v_toApplicative_2671_, 4);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_toApplicative_2671_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v_toApplicative_2671_, 1);
lean_dec(v_unused_2761_);
v___x_2680_ = v_toApplicative_2671_;
v_isShared_2681_ = v_isSharedCheck_2760_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_toSeqRight_2678_);
lean_inc(v_toSeqLeft_2677_);
lean_inc(v_toSeq_2676_);
lean_inc(v_toFunctor_2675_);
lean_dec(v_toApplicative_2671_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2760_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___f_2682_; lean_object* v___f_2683_; lean_object* v___f_2684_; lean_object* v___f_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___f_2689_; lean_object* v___x_2691_; 
v___f_2682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(v_toFunctor_2675_);
v___f_2684_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2684_, 0, v_toFunctor_2675_);
v___f_2685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2685_, 0, v_toFunctor_2675_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___f_2684_);
lean_ctor_set(v___x_2686_, 1, v___f_2685_);
v___f_2687_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2687_, 0, v_toSeqRight_2678_);
v___f_2688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2688_, 0, v_toSeqLeft_2677_);
v___f_2689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2689_, 0, v_toSeq_2676_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 4, v___f_2687_);
lean_ctor_set(v___x_2680_, 3, v___f_2688_);
lean_ctor_set(v___x_2680_, 2, v___f_2689_);
lean_ctor_set(v___x_2680_, 1, v___f_2682_);
lean_ctor_set(v___x_2680_, 0, v___x_2686_);
v___x_2691_ = v___x_2680_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___f_2682_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v___f_2689_);
lean_ctor_set(v_reuseFailAlloc_2759_, 3, v___f_2688_);
lean_ctor_set(v_reuseFailAlloc_2759_, 4, v___f_2687_);
v___x_2691_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 1, v___f_2683_);
lean_ctor_set(v___x_2673_, 0, v___x_2691_);
v___x_2693_ = v___x_2673_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2691_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___f_2683_);
v___x_2693_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v_toApplicative_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2756_; 
v___x_2694_ = l_ReaderT_instMonad___redArg(v___x_2693_);
v_toApplicative_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; 
v_unused_2757_ = lean_ctor_get(v___x_2694_, 1);
lean_dec(v_unused_2757_);
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2756_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_toApplicative_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2756_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v_toFunctor_2699_; lean_object* v_toSeq_2700_; lean_object* v_toSeqLeft_2701_; lean_object* v_toSeqRight_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2754_; 
v_toFunctor_2699_ = lean_ctor_get(v_toApplicative_2695_, 0);
v_toSeq_2700_ = lean_ctor_get(v_toApplicative_2695_, 2);
v_toSeqLeft_2701_ = lean_ctor_get(v_toApplicative_2695_, 3);
v_toSeqRight_2702_ = lean_ctor_get(v_toApplicative_2695_, 4);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_toApplicative_2695_);
if (v_isSharedCheck_2754_ == 0)
{
lean_object* v_unused_2755_; 
v_unused_2755_ = lean_ctor_get(v_toApplicative_2695_, 1);
lean_dec(v_unused_2755_);
v___x_2704_ = v_toApplicative_2695_;
v_isShared_2705_ = v_isSharedCheck_2754_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_toSeqRight_2702_);
lean_inc(v_toSeqLeft_2701_);
lean_inc(v_toSeq_2700_);
lean_inc(v_toFunctor_2699_);
lean_dec(v_toApplicative_2695_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2754_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___f_2712_; lean_object* v___f_2713_; lean_object* v___x_2715_; 
v___f_2706_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2707_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2699_);
v___f_2708_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2708_, 0, v_toFunctor_2699_);
v___f_2709_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2709_, 0, v_toFunctor_2699_);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___f_2708_);
lean_ctor_set(v___x_2710_, 1, v___f_2709_);
v___f_2711_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2711_, 0, v_toSeqRight_2702_);
v___f_2712_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2712_, 0, v_toSeqLeft_2701_);
v___f_2713_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2713_, 0, v_toSeq_2700_);
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 4, v___f_2711_);
lean_ctor_set(v___x_2704_, 3, v___f_2712_);
lean_ctor_set(v___x_2704_, 2, v___f_2713_);
lean_ctor_set(v___x_2704_, 1, v___f_2706_);
lean_ctor_set(v___x_2704_, 0, v___x_2710_);
v___x_2715_ = v___x_2704_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2753_, 1, v___f_2706_);
lean_ctor_set(v_reuseFailAlloc_2753_, 2, v___f_2713_);
lean_ctor_set(v_reuseFailAlloc_2753_, 3, v___f_2712_);
lean_ctor_set(v_reuseFailAlloc_2753_, 4, v___f_2711_);
v___x_2715_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2717_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___f_2707_);
lean_ctor_set(v___x_2697_, 0, v___x_2715_);
v___x_2717_ = v___x_2697_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___f_2707_);
v___x_2717_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; 
v___x_2718_ = l_ReaderT_instMonad___redArg(v___x_2717_);
v___x_2719_ = l_ReaderT_instMonad___redArg(v___x_2718_);
v___x_2720_ = l_ReaderT_instMonad___redArg(v___x_2719_);
v___x_2721_ = l_ReaderT_instMonad___redArg(v___x_2720_);
v___x_2722_ = l_ReaderT_instMonad___redArg(v___x_2721_);
v___x_2723_ = l_ReaderT_instMonad___redArg(v___x_2722_);
v___x_2724_ = l_ReaderT_instMonad___redArg(v___x_2723_);
v___f_2725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1);
v___x_2726_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2743_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2729_ = v___x_2726_;
v_isShared_2730_ = v_isSharedCheck_2743_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2726_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2743_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___f_2731_; lean_object* v_cnstrsOf_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___f_2731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2732_ = lean_ctor_get(v_a_2727_, 17);
lean_inc_ref(v_cnstrsOf_2732_);
lean_dec(v_a_2727_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v_u_2655_);
lean_ctor_set(v___x_2733_, 1, v_v_2656_);
v___x_2734_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2731_, v___f_2725_, v_cnstrsOf_2732_, v___x_2733_);
if (lean_obj_tag(v___x_2734_) == 1)
{
lean_object* v_val_2735_; lean_object* v___f_2736_; lean_object* v___x_1569__overap_2737_; lean_object* v___x_2738_; 
lean_del_object(v___x_2729_);
v_val_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_val_2735_);
lean_dec_ref(v___x_2734_);
v___f_2736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2736_, 0, v_f_2657_);
v___x_1569__overap_2737_ = l_List_forM___redArg(v___x_2724_, v_val_2735_, v___f_2736_);
v___x_2738_ = lean_apply_12(v___x_1569__overap_2737_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, lean_box(0));
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec(v___x_2734_);
lean_dec_ref(v___x_2724_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_f_2657_);
v___x_2739_ = lean_box(0);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 0, v___x_2739_);
v___x_2741_ = v___x_2729_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec_ref(v___x_2724_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_f_2657_);
lean_dec(v_v_2656_);
lean_dec(v_u_2655_);
v_a_2744_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2726_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2726_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2764_, lean_object* v_v_2765_, lean_object* v_f_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2764_, v_v_2765_, v_f_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2781_, v_a_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2807_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2807_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2807_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_termMapInv_2789_; lean_object* v___x_2790_; 
v_termMapInv_2789_ = lean_ctor_get(v_a_2785_, 4);
lean_inc_ref(v_termMapInv_2789_);
lean_dec(v_a_2785_);
v___x_2790_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2789_, v_e_2780_);
if (lean_obj_tag(v___x_2790_) == 1)
{
lean_object* v_val_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2802_; 
v_val_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_val_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2802_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_fst_2795_; lean_object* v___x_2797_; 
v_fst_2795_ = lean_ctor_get(v_val_2791_, 0);
lean_inc(v_fst_2795_);
lean_dec(v_val_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_fst_2795_);
v___x_2797_ = v___x_2793_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_fst_2795_);
v___x_2797_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2799_; 
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2797_);
v___x_2799_ = v___x_2787_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
lean_dec(v___x_2790_);
v___x_2803_ = lean_box(0);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2803_);
v___x_2805_ = v___x_2787_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2784_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2784_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2816_, v_a_2817_, v_a_2818_);
lean_dec_ref(v_a_2818_);
lean_dec(v_a_2817_);
lean_dec_ref(v_e_2816_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2821_, v_a_2822_, v_a_2830_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_e_2834_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2847_, lean_object* v_v_2848_, lean_object* v_k_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; uint8_t v___x_2905_; 
v___x_2905_ = lean_nat_dec_eq(v_u_2847_, v_v_2848_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3043_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_3043_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3043_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_unbox(v_a_2907_);
lean_dec(v_a_2907_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_del_object(v___x_2909_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
return v___x_2918_;
}
else
{
uint8_t v___x_2919_; 
v___x_2919_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2849_);
if (v___x_2919_ == 0)
{
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
goto v___jp_2911_;
}
else
{
if (v___x_2905_ == 0)
{
lean_object* v___x_2920_; 
lean_del_object(v___x_2909_);
v___x_2920_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_2848_, v_u_2847_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3034_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_2923_ = v___x_2920_;
v_isShared_2924_ = v_isSharedCheck_3034_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2920_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3034_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
if (lean_obj_tag(v_a_2921_) == 1)
{
lean_object* v_val_2925_; uint8_t v___x_2926_; 
v_val_2925_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_val_2925_);
lean_dec_ref(v_a_2921_);
v___x_2926_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2925_);
lean_dec(v_val_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2927_ = lean_box(0);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_2927_);
v___x_2929_ = v___x_2923_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2927_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
else
{
lean_object* v___x_2931_; 
lean_del_object(v___x_2923_);
v___x_2931_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2847_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2848_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___y_2936_; lean_object* v___x_3010_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref(v___x_2933_);
v___x_3010_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2932_, v_a_2851_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; uint8_t v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
v___x_3012_ = lean_unbox(v_a_3011_);
lean_dec(v_a_3011_);
if (v___x_3012_ == 0)
{
v___y_2936_ = v___x_3010_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_3013_; 
lean_dec_ref(v___x_3010_);
v___x_3013_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2934_, v_a_2851_);
v___y_2936_ = v___x_3013_;
goto v___jp_2935_;
}
}
else
{
v___y_2936_ = v___x_3010_;
goto v___jp_2935_;
}
v___jp_2935_:
{
if (lean_obj_tag(v___y_2936_) == 0)
{
lean_object* v_a_2937_; uint8_t v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___y_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref(v___y_2936_);
v___x_2938_ = lean_unbox(v_a_2937_);
lean_dec(v_a_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2932_, v_a_2851_, v_a_2859_);
lean_dec(v_a_2932_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2972_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_2972_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2972_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
if (lean_obj_tag(v_a_2940_) == 1)
{
lean_object* v_val_2944_; lean_object* v___x_2945_; 
lean_del_object(v___x_2942_);
v_val_2944_ = lean_ctor_get(v_a_2940_, 0);
lean_inc(v_val_2944_);
lean_dec_ref(v_a_2940_);
v___x_2945_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2934_, v_a_2851_, v_a_2859_);
lean_dec(v_a_2934_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2959_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
if (lean_obj_tag(v_a_2946_) == 1)
{
lean_object* v_val_2950_; lean_object* v___x_2951_; 
lean_del_object(v___x_2948_);
v_val_2950_ = lean_ctor_get(v_a_2946_, 0);
lean_inc(v_val_2950_);
lean_dec_ref(v_a_2946_);
v___x_2951_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2944_, v_a_2851_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; uint8_t v___x_2953_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
v___x_2953_ = lean_unbox(v_a_2952_);
lean_dec(v_a_2952_);
if (v___x_2953_ == 0)
{
v___y_2863_ = v_val_2950_;
v___y_2864_ = v_val_2944_;
v___y_2865_ = v___x_2951_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2954_; 
lean_dec_ref(v___x_2951_);
v___x_2954_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2950_, v_a_2851_);
v___y_2863_ = v_val_2950_;
v___y_2864_ = v_val_2944_;
v___y_2865_ = v___x_2954_;
goto v___jp_2862_;
}
}
else
{
v___y_2863_ = v_val_2950_;
v___y_2864_ = v_val_2944_;
v___y_2865_ = v___x_2951_;
goto v___jp_2862_;
}
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2957_; 
lean_dec(v_a_2946_);
lean_dec(v_val_2944_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2955_ = lean_box(0);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2955_);
v___x_2957_ = v___x_2948_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_val_2944_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_2960_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2945_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2945_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_dec(v_a_2940_);
lean_dec(v_a_2934_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2968_ = lean_box(0);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2968_);
v___x_2970_ = v___x_2942_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec(v_a_2934_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_2973_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2939_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2939_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
else
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2932_, v_a_2934_, v_a_2851_);
lean_dec(v_a_2934_);
lean_dec(v_a_2932_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2993_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2984_ = v___x_2981_;
v_isShared_2985_ = v_isSharedCheck_2993_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2981_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2993_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
uint8_t v___x_2986_; 
v___x_2986_ = lean_unbox(v_a_2982_);
lean_dec(v_a_2982_);
if (v___x_2986_ == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
lean_del_object(v___x_2984_);
v___x_2987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2987_, 0, v_u_2847_);
lean_ctor_set(v___x_2987_, 1, v_v_2848_);
v___x_2988_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2987_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2988_;
}
else
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2989_ = lean_box(0);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2989_);
v___x_2991_ = v___x_2984_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_2994_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2981_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2981_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_a_2934_);
lean_dec(v_a_2932_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_3002_ = lean_ctor_get(v___y_2936_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___y_2936_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___y_2936_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___y_2936_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_2932_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_3014_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2933_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2933_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_3022_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2931_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2931_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_dec(v_a_2921_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_3030_ = lean_box(0);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 0, v___x_3030_);
v___x_3032_ = v___x_2923_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_3035_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2920_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2920_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
goto v___jp_2911_;
}
}
}
v___jp_2911_:
{
lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2912_ = lean_box(0);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2912_);
v___x_2914_ = v___x_2909_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_3044_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2906_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2906_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
return v___x_3053_;
}
v___jp_2862_:
{
if (lean_obj_tag(v___y_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2896_; 
v_a_2866_ = lean_ctor_get(v___y_2865_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___y_2865_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2868_ = v___y_2865_;
v_isShared_2869_ = v_isSharedCheck_2896_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___y_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2896_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
uint8_t v___x_2870_; 
v___x_2870_ = lean_unbox(v_a_2866_);
lean_dec(v_a_2866_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2871_ = lean_box(0);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2871_);
v___x_2873_ = v___x_2868_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
else
{
lean_object* v___x_2875_; 
lean_del_object(v___x_2868_);
v___x_2875_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2864_, v___y_2863_, v_a_2851_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v___y_2864_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_unbox(v_a_2876_);
lean_dec(v_a_2876_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_del_object(v___x_2878_);
v___x_2881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2881_, 0, v_u_2847_);
lean_ctor_set(v___x_2881_, 1, v_v_2848_);
v___x_2882_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2881_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v___x_2883_ = lean_box(0);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2883_);
v___x_2885_ = v___x_2878_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
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
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_2888_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2875_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2875_);
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
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v_a_2850_);
lean_dec(v_v_2848_);
lean_dec(v_u_2847_);
v_a_2897_ = lean_ctor_get(v___y_2865_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___y_2865_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___y_2865_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___y_2865_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_3054_, lean_object* v_v_3055_, lean_object* v_k_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3054_, v_v_3055_, v_k_3056_, v_a_3057_, v_a_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_k_3056_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_3070_, lean_object* v_vals_3071_, lean_object* v_i_3072_, lean_object* v_k_3073_){
_start:
{
uint8_t v___y_3075_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = lean_array_get_size(v_keys_3070_);
v___x_3082_ = lean_nat_dec_lt(v_i_3072_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v_i_3072_);
v___x_3083_ = lean_box(0);
return v___x_3083_;
}
else
{
lean_object* v_fst_3084_; lean_object* v_snd_3085_; lean_object* v_k_x27_3086_; lean_object* v_fst_3087_; lean_object* v_snd_3088_; uint8_t v___x_3089_; 
v_fst_3084_ = lean_ctor_get(v_k_3073_, 0);
v_snd_3085_ = lean_ctor_get(v_k_3073_, 1);
v_k_x27_3086_ = lean_array_fget_borrowed(v_keys_3070_, v_i_3072_);
v_fst_3087_ = lean_ctor_get(v_k_x27_3086_, 0);
v_snd_3088_ = lean_ctor_get(v_k_x27_3086_, 1);
v___x_3089_ = lean_nat_dec_eq(v_fst_3084_, v_fst_3087_);
if (v___x_3089_ == 0)
{
v___y_3075_ = v___x_3089_;
goto v___jp_3074_;
}
else
{
uint8_t v___x_3090_; 
v___x_3090_ = lean_nat_dec_eq(v_snd_3085_, v_snd_3088_);
v___y_3075_ = v___x_3090_;
goto v___jp_3074_;
}
}
v___jp_3074_:
{
if (v___y_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = lean_unsigned_to_nat(1u);
v___x_3077_ = lean_nat_add(v_i_3072_, v___x_3076_);
lean_dec(v_i_3072_);
v_i_3072_ = v___x_3077_;
goto _start;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_array_fget_borrowed(v_vals_3071_, v_i_3072_);
lean_dec(v_i_3072_);
lean_inc(v___x_3079_);
v___x_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
return v___x_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_3091_, lean_object* v_vals_3092_, lean_object* v_i_3093_, lean_object* v_k_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3091_, v_vals_3092_, v_i_3093_, v_k_3094_);
lean_dec_ref(v_k_3094_);
lean_dec_ref(v_vals_3092_);
lean_dec_ref(v_keys_3091_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_3096_, size_t v_x_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_es_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3127_; 
v_es_3099_ = lean_ctor_get(v_x_3096_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_x_3096_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3101_ = v_x_3096_;
v_isShared_3102_ = v_isSharedCheck_3127_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_es_3099_);
lean_dec(v_x_3096_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3127_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; lean_object* v_j_3107_; lean_object* v___x_3108_; 
v___x_3103_ = lean_box(2);
v___x_3104_ = ((size_t)5ULL);
v___x_3105_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1);
v___x_3106_ = lean_usize_land(v_x_3097_, v___x_3105_);
v_j_3107_ = lean_usize_to_nat(v___x_3106_);
v___x_3108_ = lean_array_get(v___x_3103_, v_es_3099_, v_j_3107_);
lean_dec(v_j_3107_);
lean_dec_ref(v_es_3099_);
switch(lean_obj_tag(v___x_3108_))
{
case 0:
{
lean_object* v_key_3109_; lean_object* v_val_3110_; uint8_t v___y_3112_; lean_object* v_fst_3117_; lean_object* v_snd_3118_; lean_object* v_fst_3119_; lean_object* v_snd_3120_; uint8_t v___x_3121_; 
v_key_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_key_3109_);
v_val_3110_ = lean_ctor_get(v___x_3108_, 1);
lean_inc(v_val_3110_);
lean_dec_ref(v___x_3108_);
v_fst_3117_ = lean_ctor_get(v_x_3098_, 0);
v_snd_3118_ = lean_ctor_get(v_x_3098_, 1);
v_fst_3119_ = lean_ctor_get(v_key_3109_, 0);
lean_inc(v_fst_3119_);
v_snd_3120_ = lean_ctor_get(v_key_3109_, 1);
lean_inc(v_snd_3120_);
lean_dec(v_key_3109_);
v___x_3121_ = lean_nat_dec_eq(v_fst_3117_, v_fst_3119_);
lean_dec(v_fst_3119_);
if (v___x_3121_ == 0)
{
lean_dec(v_snd_3120_);
v___y_3112_ = v___x_3121_;
goto v___jp_3111_;
}
else
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_eq(v_snd_3118_, v_snd_3120_);
lean_dec(v_snd_3120_);
v___y_3112_ = v___x_3122_;
goto v___jp_3111_;
}
v___jp_3111_:
{
if (v___y_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec(v_val_3110_);
lean_del_object(v___x_3101_);
v___x_3113_ = lean_box(0);
return v___x_3113_;
}
else
{
lean_object* v___x_3115_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set_tag(v___x_3101_, 1);
lean_ctor_set(v___x_3101_, 0, v_val_3110_);
v___x_3115_ = v___x_3101_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_val_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
case 1:
{
lean_object* v_node_3123_; size_t v___x_3124_; 
lean_del_object(v___x_3101_);
v_node_3123_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_node_3123_);
lean_dec_ref(v___x_3108_);
v___x_3124_ = lean_usize_shift_right(v_x_3097_, v___x_3104_);
v_x_3096_ = v_node_3123_;
v_x_3097_ = v___x_3124_;
goto _start;
}
default: 
{
lean_object* v___x_3126_; 
lean_del_object(v___x_3101_);
v___x_3126_ = lean_box(0);
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_ks_3128_; lean_object* v_vs_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_ks_3128_ = lean_ctor_get(v_x_3096_, 0);
lean_inc_ref(v_ks_3128_);
v_vs_3129_ = lean_ctor_get(v_x_3096_, 1);
lean_inc_ref(v_vs_3129_);
lean_dec_ref(v_x_3096_);
v___x_3130_ = lean_unsigned_to_nat(0u);
v___x_3131_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_3128_, v_vs_3129_, v___x_3130_, v_x_3098_);
lean_dec_ref(v_vs_3129_);
lean_dec_ref(v_ks_3128_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
size_t v_x_4035__boxed_3135_; lean_object* v_res_3136_; 
v_x_4035__boxed_3135_ = lean_unbox_usize(v_x_3133_);
lean_dec(v_x_3133_);
v_res_3136_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3132_, v_x_4035__boxed_3135_, v_x_3134_);
lean_dec_ref(v_x_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_3137_, lean_object* v_x_3138_){
_start:
{
lean_object* v_fst_3139_; lean_object* v_snd_3140_; uint64_t v___x_3141_; uint64_t v___x_3142_; uint64_t v___x_3143_; size_t v___x_3144_; lean_object* v___x_3145_; 
v_fst_3139_ = lean_ctor_get(v_x_3138_, 0);
v_snd_3140_ = lean_ctor_get(v_x_3138_, 1);
v___x_3141_ = lean_uint64_of_nat(v_fst_3139_);
v___x_3142_ = lean_uint64_of_nat(v_snd_3140_);
v___x_3143_ = lean_uint64_mix_hash(v___x_3141_, v___x_3142_);
v___x_3144_ = lean_uint64_to_usize(v___x_3143_);
v___x_3145_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3137_, v___x_3144_, v_x_3138_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3146_, lean_object* v_x_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3146_, v_x_3147_);
lean_dec_ref(v_x_3147_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3149_, lean_object* v_v_3150_, lean_object* v_k_3151_, lean_object* v_as_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
if (lean_obj_tag(v_as_3152_) == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec(v___y_3153_);
lean_dec_ref(v_k_3151_);
lean_dec(v_v_3150_);
lean_dec(v_u_3149_);
v___x_3165_ = lean_box(0);
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
return v___x_3166_;
}
else
{
lean_object* v_head_3167_; lean_object* v_tail_3168_; lean_object* v_fst_3169_; lean_object* v_snd_3170_; lean_object* v___x_3171_; 
v_head_3167_ = lean_ctor_get(v_as_3152_, 0);
lean_inc(v_head_3167_);
v_tail_3168_ = lean_ctor_get(v_as_3152_, 1);
lean_inc(v_tail_3168_);
lean_dec_ref(v_as_3152_);
v_fst_3169_ = lean_ctor_get(v_head_3167_, 0);
lean_inc(v_fst_3169_);
v_snd_3170_ = lean_ctor_get(v_head_3167_, 1);
lean_inc(v_snd_3170_);
lean_dec(v_head_3167_);
lean_inc(v___y_3153_);
lean_inc_ref(v_k_3151_);
lean_inc(v_v_3150_);
lean_inc(v_u_3149_);
v___x_3171_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3149_, v_v_3150_, v_k_3151_, v_fst_3169_, v_snd_3170_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref(v___x_3171_);
v_as_3152_ = v_tail_3168_;
goto _start;
}
else
{
lean_dec(v_tail_3168_);
lean_dec(v___y_3153_);
lean_dec_ref(v_k_3151_);
lean_dec(v_v_3150_);
lean_dec(v_u_3149_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3173_, lean_object* v_v_3174_, lean_object* v_k_3175_, lean_object* v_as_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3173_, v_v_3174_, v_k_3175_, v_as_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
lean_dec(v___y_3179_);
lean_dec(v___y_3178_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3190_, lean_object* v_v_3191_, lean_object* v_k_3192_, lean_object* v_as_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
if (lean_obj_tag(v_as_3193_) == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
lean_dec(v___y_3194_);
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
v___x_3206_ = lean_box(0);
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3206_);
return v___x_3207_;
}
else
{
lean_object* v_head_3208_; lean_object* v_tail_3209_; lean_object* v_fst_3210_; lean_object* v_snd_3211_; lean_object* v___x_3212_; 
v_head_3208_ = lean_ctor_get(v_as_3193_, 0);
lean_inc(v_head_3208_);
v_tail_3209_ = lean_ctor_get(v_as_3193_, 1);
lean_inc(v_tail_3209_);
lean_dec_ref(v_as_3193_);
v_fst_3210_ = lean_ctor_get(v_head_3208_, 0);
lean_inc(v_fst_3210_);
v_snd_3211_ = lean_ctor_get(v_head_3208_, 1);
lean_inc(v_snd_3211_);
lean_dec(v_head_3208_);
lean_inc(v___y_3194_);
lean_inc_ref(v_k_3192_);
lean_inc(v_v_3191_);
lean_inc(v_u_3190_);
v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3190_, v_v_3191_, v_k_3192_, v_fst_3210_, v_snd_3211_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref(v___x_3212_);
v_as_3193_ = v_tail_3209_;
goto _start;
}
else
{
lean_dec(v_tail_3209_);
lean_dec(v___y_3194_);
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
return v___x_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3214_, lean_object* v_v_3215_, lean_object* v_k_3216_, lean_object* v_as_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3214_, v_v_3215_, v_k_3216_, v_as_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec(v___y_3219_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3231_, lean_object* v_v_3232_, lean_object* v_k_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v_cnstrsOf_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref(v___x_3264_);
v_cnstrsOf_3266_ = lean_ctor_get(v_a_3265_, 17);
lean_inc_ref(v_cnstrsOf_3266_);
lean_dec(v_a_3265_);
lean_inc(v_v_3232_);
lean_inc(v_u_3231_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_u_3231_);
lean_ctor_set(v___x_3267_, 1, v_v_3232_);
v___x_3268_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3266_, v___x_3267_);
lean_dec_ref(v___x_3267_);
if (lean_obj_tag(v___x_3268_) == 1)
{
lean_object* v_val_3269_; lean_object* v___x_3270_; 
v_val_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_val_3269_);
lean_dec_ref(v___x_3268_);
lean_inc(v_a_3234_);
lean_inc_ref(v_k_3233_);
lean_inc(v_v_3232_);
lean_inc(v_u_3231_);
v___x_3270_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3231_, v_v_3232_, v_k_3233_, v_val_3269_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref(v___x_3270_);
goto v___jp_3246_;
}
else
{
lean_dec(v_a_3234_);
lean_dec_ref(v_k_3233_);
lean_dec(v_v_3232_);
lean_dec(v_u_3231_);
return v___x_3270_;
}
}
else
{
lean_dec(v___x_3268_);
goto v___jp_3246_;
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_a_3234_);
lean_dec_ref(v_k_3233_);
lean_dec(v_v_3232_);
lean_dec(v_u_3231_);
v_a_3271_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3264_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3264_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
v___jp_3246_:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v_cnstrsOf_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3247_);
v_cnstrsOf_3249_ = lean_ctor_get(v_a_3248_, 17);
lean_inc_ref(v_cnstrsOf_3249_);
lean_dec(v_a_3248_);
lean_inc(v_u_3231_);
lean_inc(v_v_3232_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v_v_3232_);
lean_ctor_set(v___x_3250_, 1, v_u_3231_);
v___x_3251_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3249_, v___x_3250_);
lean_dec_ref(v___x_3250_);
if (lean_obj_tag(v___x_3251_) == 1)
{
lean_object* v_val_3252_; lean_object* v___x_3253_; 
v_val_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_val_3252_);
lean_dec_ref(v___x_3251_);
lean_inc(v_a_3234_);
lean_inc_ref(v_k_3233_);
lean_inc(v_v_3232_);
lean_inc(v_u_3231_);
v___x_3253_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3231_, v_v_3232_, v_k_3233_, v_val_3252_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref(v___x_3253_);
v___x_3254_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3231_, v_v_3232_, v_k_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec_ref(v_k_3233_);
return v___x_3254_;
}
else
{
lean_dec(v_a_3234_);
lean_dec_ref(v_k_3233_);
lean_dec(v_v_3232_);
lean_dec(v_u_3231_);
return v___x_3253_;
}
}
else
{
lean_object* v___x_3255_; 
lean_dec(v___x_3251_);
v___x_3255_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3231_, v_v_3232_, v_k_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_);
lean_dec_ref(v_k_3233_);
return v___x_3255_;
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_a_3234_);
lean_dec_ref(v_k_3233_);
lean_dec(v_v_3232_);
lean_dec(v_u_3231_);
v_a_3256_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3247_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3247_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3279_, lean_object* v_v_3280_, lean_object* v_k_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3279_, v_v_3280_, v_k_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3295_, lean_object* v_x_3296_, lean_object* v_x_3297_){
_start:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3296_, v_x_3297_);
return v___x_3298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3299_, lean_object* v_x_3300_, lean_object* v_x_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3299_, v_x_3300_, v_x_3301_);
lean_dec_ref(v_x_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3303_, lean_object* v_x_3304_, size_t v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3304_, v_x_3305_, v_x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3308_, lean_object* v_x_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
size_t v_x_4348__boxed_3312_; lean_object* v_res_3313_; 
v_x_4348__boxed_3312_ = lean_unbox_usize(v_x_3310_);
lean_dec(v_x_3310_);
v_res_3313_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3308_, v_x_3309_, v_x_4348__boxed_3312_, v_x_3311_);
lean_dec_ref(v_x_3311_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3314_, lean_object* v_keys_3315_, lean_object* v_vals_3316_, lean_object* v_heq_3317_, lean_object* v_i_3318_, lean_object* v_k_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3315_, v_vals_3316_, v_i_3318_, v_k_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3321_, lean_object* v_keys_3322_, lean_object* v_vals_3323_, lean_object* v_heq_3324_, lean_object* v_i_3325_, lean_object* v_k_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3321_, v_keys_3322_, v_vals_3323_, v_heq_3324_, v_i_3325_, v_k_3326_);
lean_dec_ref(v_k_3326_);
lean_dec_ref(v_vals_3323_);
lean_dec_ref(v_keys_3322_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3328_, lean_object* v_v_3329_, lean_object* v_k_3330_, lean_object* v_w_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3328_, v_v_3329_, v_k_3330_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3367_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3367_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3367_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
uint8_t v___x_3349_; 
v___x_3349_ = lean_unbox(v_a_3345_);
lean_dec(v_a_3345_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
lean_dec(v_a_3332_);
lean_dec_ref(v_k_3330_);
lean_dec(v_v_3329_);
lean_dec(v_u_3328_);
v___x_3350_ = lean_box(0);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3350_);
v___x_3352_ = v___x_3347_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
else
{
lean_object* v___x_3354_; 
lean_del_object(v___x_3347_);
lean_inc(v_a_3332_);
lean_inc_ref(v_k_3330_);
lean_inc(v_v_3329_);
lean_inc(v_u_3328_);
v___x_3354_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3328_, v_v_3329_, v_k_3330_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v___x_3355_; 
lean_dec_ref(v___x_3354_);
v___x_3355_ = l_Lean_Meta_Grind_Order_getProof(v_w_3331_, v_v_3329_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3357_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref(v___x_3355_);
lean_inc(v_a_3332_);
lean_inc(v_v_3329_);
lean_inc(v_u_3328_);
v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3328_, v_v_3329_, v_a_3356_, v_a_3332_, v_a_3333_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v___x_3358_; 
lean_dec_ref(v___x_3357_);
v___x_3358_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3328_, v_v_3329_, v_k_3330_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
return v___x_3358_;
}
else
{
lean_dec(v_a_3332_);
lean_dec_ref(v_k_3330_);
lean_dec(v_v_3329_);
lean_dec(v_u_3328_);
return v___x_3357_;
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_a_3332_);
lean_dec_ref(v_k_3330_);
lean_dec(v_v_3329_);
lean_dec(v_u_3328_);
v_a_3359_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3355_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3355_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_dec(v_a_3332_);
lean_dec_ref(v_k_3330_);
lean_dec(v_v_3329_);
lean_dec(v_u_3328_);
return v___x_3354_;
}
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec(v_a_3332_);
lean_dec_ref(v_k_3330_);
lean_dec(v_v_3329_);
lean_dec(v_u_3328_);
v_a_3368_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3344_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3344_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3376_, lean_object* v_v_3377_, lean_object* v_k_3378_, lean_object* v_w_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3376_, v_v_3377_, v_k_3378_, v_w_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
lean_dec(v_a_3390_);
lean_dec_ref(v_a_3389_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_a_3384_);
lean_dec_ref(v_a_3383_);
lean_dec(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec(v_w_3379_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3393_, lean_object* v_i_3394_, lean_object* v_v_3395_, lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec(v___y_3397_);
lean_dec(v_i_3394_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
else
{
lean_object* v_key_3411_; lean_object* v_value_3412_; lean_object* v_tail_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; 
v_key_3411_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_key_3411_);
v_value_3412_ = lean_ctor_get(v_x_3396_, 1);
lean_inc(v_value_3412_);
v_tail_3413_ = lean_ctor_get(v_x_3396_, 2);
lean_inc(v_tail_3413_);
lean_dec_ref(v_x_3396_);
v___x_3414_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3393_, v_value_3412_);
lean_inc(v___y_3397_);
lean_inc(v_i_3394_);
v___x_3415_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3394_, v_key_3411_, v___x_3414_, v_v_3395_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_dec_ref(v___x_3415_);
v_x_3396_ = v_tail_3413_;
goto _start;
}
else
{
lean_dec(v_tail_3413_);
lean_dec(v___y_3397_);
lean_dec(v_i_3394_);
return v___x_3415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3417_, lean_object* v_i_3418_, lean_object* v_v_3419_, lean_object* v_x_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3417_, v_i_3418_, v_v_3419_, v_x_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec(v_v_3419_);
lean_dec_ref(v___x_3417_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3434_, lean_object* v_v_3435_, lean_object* v_u_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
if (lean_obj_tag(v_x_3437_) == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec(v___y_3438_);
lean_dec(v_v_3435_);
lean_dec_ref(v_k_3434_);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
return v___x_3451_;
}
else
{
lean_object* v_key_3452_; lean_object* v_value_3453_; lean_object* v_tail_3454_; lean_object* v___y_3456_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_key_3452_ = lean_ctor_get(v_x_3437_, 0);
lean_inc(v_key_3452_);
v_value_3453_ = lean_ctor_get(v_x_3437_, 1);
lean_inc(v_value_3453_);
v_tail_3454_ = lean_ctor_get(v_x_3437_, 2);
lean_inc(v_tail_3454_);
lean_dec_ref(v_x_3437_);
lean_inc_ref(v_k_3434_);
v___x_3458_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3453_, v_k_3434_);
lean_dec(v_value_3453_);
lean_inc(v___y_3438_);
lean_inc_ref(v___x_3458_);
lean_inc(v_v_3435_);
lean_inc(v_key_3452_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3452_, v_v_3435_, v___x_3458_, v_u_3436_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3460_; 
lean_dec_ref(v___x_3459_);
v___x_3460_ = l_Lean_Meta_Grind_Order_getStruct(v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_targets_3462_; lean_object* v_size_3463_; lean_object* v___x_3464_; uint8_t v___x_3465_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref(v___x_3460_);
v_targets_3462_ = lean_ctor_get(v_a_3461_, 19);
lean_inc_ref(v_targets_3462_);
lean_dec(v_a_3461_);
v_size_3463_ = lean_ctor_get(v_targets_3462_, 2);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_nat_dec_lt(v_v_3435_, v_size_3463_);
if (v___x_3465_ == 0)
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
lean_dec_ref(v_targets_3462_);
v___x_3466_ = l_outOfBounds___redArg(v___x_3464_);
lean_inc(v___y_3438_);
v___x_3467_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3458_, v_key_3452_, v_v_3435_, v___x_3466_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec_ref(v___x_3458_);
v___y_3456_ = v___x_3467_;
goto v___jp_3455_;
}
else
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3464_, v_targets_3462_, v_v_3435_);
lean_inc(v___y_3438_);
v___x_3469_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3458_, v_key_3452_, v_v_3435_, v___x_3468_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec_ref(v___x_3458_);
v___y_3456_ = v___x_3469_;
goto v___jp_3455_;
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v___x_3458_);
lean_dec(v_tail_3454_);
lean_dec(v_key_3452_);
lean_dec(v___y_3438_);
lean_dec(v_v_3435_);
lean_dec_ref(v_k_3434_);
v_a_3470_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3460_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3460_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_dec_ref(v___x_3458_);
lean_dec(v_key_3452_);
v___y_3456_ = v___x_3459_;
goto v___jp_3455_;
}
v___jp_3455_:
{
if (lean_obj_tag(v___y_3456_) == 0)
{
lean_dec_ref(v___y_3456_);
v_x_3437_ = v_tail_3454_;
goto _start;
}
else
{
lean_dec(v_tail_3454_);
lean_dec(v___y_3438_);
lean_dec(v_v_3435_);
lean_dec_ref(v_k_3434_);
return v___y_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3478_, lean_object* v_v_3479_, lean_object* v_u_3480_, lean_object* v_x_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3478_, v_v_3479_, v_u_3480_, v_x_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec(v_u_3480_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3495_, lean_object* v_v_3496_, lean_object* v_k_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_){
_start:
{
lean_object* v___y_3511_; lean_object* v___x_3530_; 
v___x_3530_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v_targets_3532_; lean_object* v_size_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref(v___x_3530_);
v_targets_3532_ = lean_ctor_get(v_a_3531_, 19);
lean_inc_ref(v_targets_3532_);
lean_dec(v_a_3531_);
v_size_3533_ = lean_ctor_get(v_targets_3532_, 2);
v___x_3534_ = lean_box(0);
v___x_3535_ = lean_nat_dec_lt(v_v_3496_, v_size_3533_);
if (v___x_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_dec_ref(v_targets_3532_);
v___x_3536_ = l_outOfBounds___redArg(v___x_3534_);
lean_inc(v_a_3498_);
lean_inc(v_u_3495_);
v___x_3537_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3497_, v_u_3495_, v_v_3496_, v___x_3536_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
v___y_3511_ = v___x_3537_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3534_, v_targets_3532_, v_v_3496_);
lean_inc(v_a_3498_);
lean_inc(v_u_3495_);
v___x_3539_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3497_, v_u_3495_, v_v_3496_, v___x_3538_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
v___y_3511_ = v___x_3539_;
goto v___jp_3510_;
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_a_3498_);
lean_dec_ref(v_k_3497_);
lean_dec(v_v_3496_);
lean_dec(v_u_3495_);
v_a_3540_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3530_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3530_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
v___jp_3510_:
{
if (lean_obj_tag(v___y_3511_) == 0)
{
lean_object* v___x_3512_; 
lean_dec_ref(v___y_3511_);
v___x_3512_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_sources_3514_; lean_object* v_size_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref(v___x_3512_);
v_sources_3514_ = lean_ctor_get(v_a_3513_, 18);
lean_inc_ref(v_sources_3514_);
lean_dec(v_a_3513_);
v_size_3515_ = lean_ctor_get(v_sources_3514_, 2);
v___x_3516_ = lean_box(0);
v___x_3517_ = lean_nat_dec_lt(v_u_3495_, v_size_3515_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_dec_ref(v_sources_3514_);
v___x_3518_ = l_outOfBounds___redArg(v___x_3516_);
v___x_3519_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3497_, v_v_3496_, v_u_3495_, v___x_3518_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
lean_dec(v_u_3495_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3516_, v_sources_3514_, v_u_3495_);
v___x_3521_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3497_, v_v_3496_, v_u_3495_, v___x_3520_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_);
lean_dec(v_u_3495_);
return v___x_3521_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_a_3498_);
lean_dec_ref(v_k_3497_);
lean_dec(v_v_3496_);
lean_dec(v_u_3495_);
v_a_3522_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3512_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3512_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_dec(v_a_3498_);
lean_dec_ref(v_k_3497_);
lean_dec(v_v_3496_);
lean_dec(v_u_3495_);
return v___y_3511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3548_, lean_object* v_v_3549_, lean_object* v_k_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3548_, v_v_3549_, v_k_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec(v_a_3552_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3570_, lean_object* v_v_3571_, lean_object* v_k_3572_, lean_object* v_h_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3575_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3742_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3742_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3742_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_unbox(v_a_3662_);
lean_dec(v_a_3662_);
if (v___x_3666_ == 0)
{
uint8_t v___x_3667_; 
lean_del_object(v___x_3664_);
v___x_3667_ = lean_nat_dec_eq(v_u_3570_, v_v_3571_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3715_; 
v___x_3668_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3669_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3668_, v_a_3583_);
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3715_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3715_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
uint8_t v___x_3674_; 
v___x_3674_ = lean_unbox(v_a_3670_);
lean_dec(v_a_3670_);
if (v___x_3674_ == 0)
{
lean_del_object(v___x_3672_);
v___y_3624_ = v_a_3574_;
v___y_3625_ = v_a_3575_;
v___y_3626_ = v_a_3576_;
v___y_3627_ = v_a_3577_;
v___y_3628_ = v_a_3578_;
v___y_3629_ = v_a_3579_;
v___y_3630_ = v_a_3580_;
v___y_3631_ = v_a_3581_;
v___y_3632_ = v_a_3582_;
v___y_3633_ = v_a_3583_;
v___y_3634_ = v_a_3584_;
goto v___jp_3623_;
}
else
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3677_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
lean_inc(v_a_3676_);
lean_dec_ref(v___x_3675_);
v___x_3677_ = l_Lean_Meta_Grind_Order_getExpr(v_v_3571_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v_k_3679_; uint8_t v_strict_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___y_3688_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref(v___x_3677_);
v_k_3679_ = lean_ctor_get(v_k_3572_, 0);
v_strict_3680_ = lean_ctor_get_uint8(v_k_3572_, sizeof(void*)*1);
v___x_3681_ = l_Lean_MessageData_ofExpr(v_a_3676_);
v___x_3682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_MessageData_ofExpr(v_a_3678_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___x_3682_);
if (v_strict_3680_ == 0)
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Int_repr(v_k_3679_);
v___y_3688_ = v___x_3695_;
goto v___jp_3687_;
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3696_ = l_Int_repr(v_k_3679_);
v___x_3697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
v___x_3698_ = lean_string_append(v___x_3696_, v___x_3697_);
v___y_3688_ = v___x_3698_;
goto v___jp_3687_;
}
v___jp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3673_ == 0)
{
lean_ctor_set_tag(v___x_3672_, 3);
lean_ctor_set(v___x_3672_, 0, v___y_3688_);
v___x_3690_ = v___x_3672_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___y_3688_);
v___x_3690_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3691_ = l_Lean_MessageData_ofFormat(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3686_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v___x_3668_, v___x_3692_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_dec_ref(v___x_3693_);
v___y_3624_ = v_a_3574_;
v___y_3625_ = v_a_3575_;
v___y_3626_ = v_a_3576_;
v___y_3627_ = v_a_3577_;
v___y_3628_ = v_a_3578_;
v___y_3629_ = v_a_3579_;
v___y_3630_ = v_a_3580_;
v___y_3631_ = v_a_3581_;
v___y_3632_ = v_a_3582_;
v___y_3633_ = v_a_3583_;
v___y_3634_ = v_a_3584_;
goto v___jp_3623_;
}
else
{
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_a_3676_);
lean_del_object(v___x_3672_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v_a_3699_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3677_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3677_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_del_object(v___x_3672_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v_a_3707_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3675_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3675_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
}
}
else
{
uint8_t v___x_3716_; 
lean_dec(v_v_3571_);
v___x_3716_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3572_);
if (v___x_3716_ == 0)
{
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_u_3570_);
goto v___jp_3658_;
}
else
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3570_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_u_3570_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v___x_3719_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3718_, v_k_3572_, v_h_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3574_);
lean_dec_ref(v_k_3572_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3721_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_a_3720_);
lean_dec_ref(v___x_3719_);
v___x_3721_ = l_Lean_Meta_Grind_closeGoal(v_a_3720_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_dec_ref(v___x_3721_);
goto v___jp_3658_;
}
else
{
return v___x_3721_;
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
v_a_3722_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3719_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3719_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
v_a_3730_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3717_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3717_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v___x_3738_ = lean_box(0);
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v___x_3738_);
v___x_3740_ = v___x_3664_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v_a_3743_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3661_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3661_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
v___jp_3586_:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3570_, v_v_3571_, v_k_3572_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3614_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3614_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3614_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_unbox(v_a_3599_);
lean_dec(v_a_3599_);
if (v___x_3603_ == 0)
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v___x_3604_ = lean_box(0);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3604_);
v___x_3606_ = v___x_3601_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
else
{
lean_object* v___x_3608_; 
lean_del_object(v___x_3601_);
lean_inc(v___y_3587_);
lean_inc_ref(v_k_3572_);
lean_inc(v_v_3571_);
lean_inc(v_u_3570_);
v___x_3608_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3570_, v_v_3571_, v_k_3572_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
lean_dec_ref(v___x_3608_);
lean_inc_ref(v_k_3572_);
lean_inc(v_u_3570_);
v___x_3609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3609_, 0, v_u_3570_);
lean_ctor_set(v___x_3609_, 1, v_k_3572_);
lean_ctor_set(v___x_3609_, 2, v_h_3573_);
lean_inc(v___y_3587_);
lean_inc(v_v_3571_);
lean_inc(v_u_3570_);
v___x_3610_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3570_, v_v_3571_, v___x_3609_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v___x_3611_; 
lean_dec_ref(v___x_3610_);
lean_inc(v___y_3587_);
lean_inc_ref(v_k_3572_);
lean_inc(v_v_3571_);
lean_inc(v_u_3570_);
v___x_3611_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3570_, v_v_3571_, v_k_3572_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v___x_3612_; 
lean_dec_ref(v___x_3611_);
lean_inc(v___y_3587_);
v___x_3612_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3570_, v_v_3571_, v_k_3572_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref(v___x_3612_);
v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
return v___x_3613_;
}
else
{
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
return v___x_3612_;
}
}
else
{
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
return v___x_3611_;
}
}
else
{
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
return v___x_3610_;
}
}
else
{
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
return v___x_3608_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___y_3595_);
lean_dec_ref(v___y_3594_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec(v___y_3587_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v_a_3615_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3598_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3598_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
v___jp_3623_:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_3571_, v_u_3570_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
if (lean_obj_tag(v_a_3636_) == 1)
{
lean_object* v_val_3637_; lean_object* v___x_3638_; uint8_t v___x_3639_; 
v_val_3637_ = lean_ctor_get(v_a_3636_, 0);
lean_inc(v_val_3637_);
lean_dec_ref(v_a_3636_);
lean_inc(v_val_3637_);
v___x_3638_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3572_, v_val_3637_);
v___x_3639_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3638_);
lean_dec_ref(v___x_3638_);
if (v___x_3639_ == 0)
{
lean_dec(v_val_3637_);
v___y_3587_ = v___y_3624_;
v___y_3588_ = v___y_3625_;
v___y_3589_ = v___y_3626_;
v___y_3590_ = v___y_3627_;
v___y_3591_ = v___y_3628_;
v___y_3592_ = v___y_3629_;
v___y_3593_ = v___y_3630_;
v___y_3594_ = v___y_3631_;
v___y_3595_ = v___y_3632_;
v___y_3596_ = v___y_3633_;
v___y_3597_ = v___y_3634_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3640_; 
v___x_3640_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3570_, v_v_3571_, v_k_3572_, v_h_3573_, v_val_3637_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v_val_3637_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3648_; 
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3648_ == 0)
{
lean_object* v_unused_3649_; 
v_unused_3649_ = lean_ctor_get(v___x_3640_, 0);
lean_dec(v_unused_3649_);
v___x_3642_ = v___x_3640_;
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v___x_3640_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3648_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3644_ = lean_box(0);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3644_);
v___x_3646_ = v___x_3642_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
else
{
return v___x_3640_;
}
}
}
else
{
lean_dec(v_a_3636_);
v___y_3587_ = v___y_3624_;
v___y_3588_ = v___y_3625_;
v___y_3589_ = v___y_3626_;
v___y_3590_ = v___y_3627_;
v___y_3591_ = v___y_3628_;
v___y_3592_ = v___y_3629_;
v___y_3593_ = v___y_3630_;
v___y_3594_ = v___y_3631_;
v___y_3595_ = v___y_3632_;
v___y_3596_ = v___y_3633_;
v___y_3597_ = v___y_3634_;
goto v___jp_3586_;
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v_h_3573_);
lean_dec_ref(v_k_3572_);
lean_dec(v_v_3571_);
lean_dec(v_u_3570_);
v_a_3650_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3635_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3635_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
v___jp_3658_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3751_, lean_object* v_v_3752_, lean_object* v_k_3753_, lean_object* v_h_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3751_, v_v_3752_, v_k_3753_, v_h_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
return v_res_3767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = lean_box(0);
v___x_3775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3776_ = l_Lean_mkConst(v___x_3775_, v___x_3774_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3782_, lean_object* v_e_3783_, lean_object* v_he_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; uint8_t v___y_3813_; lean_object* v_h_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_cls_3857_; lean_object* v___x_3858_; lean_object* v_a_3859_; uint8_t v___x_3860_; 
v_cls_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3858_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3857_, v_a_3794_);
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___x_3858_);
v___x_3860_ = lean_unbox(v_a_3859_);
lean_dec(v_a_3859_);
if (v___x_3860_ == 0)
{
v___y_3839_ = v_a_3785_;
v___y_3840_ = v_a_3786_;
v___y_3841_ = v_a_3787_;
v___y_3842_ = v_a_3788_;
v___y_3843_ = v_a_3789_;
v___y_3844_ = v_a_3790_;
v___y_3845_ = v_a_3791_;
v___y_3846_ = v_a_3792_;
v___y_3847_ = v_a_3793_;
v___y_3848_ = v_a_3794_;
v___y_3849_ = v_a_3795_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3782_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
if (lean_obj_tag(v___x_3861_) == 0)
{
lean_object* v_a_3862_; lean_object* v___x_3863_; 
v_a_3862_ = lean_ctor_get(v___x_3861_, 0);
lean_inc(v_a_3862_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v_cls_3857_, v_a_3862_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_dec_ref(v___x_3863_);
v___y_3839_ = v_a_3785_;
v___y_3840_ = v_a_3786_;
v___y_3841_ = v_a_3787_;
v___y_3842_ = v_a_3788_;
v___y_3843_ = v_a_3789_;
v___y_3844_ = v_a_3790_;
v___y_3845_ = v_a_3791_;
v___y_3846_ = v_a_3792_;
v___y_3847_ = v_a_3793_;
v___y_3848_ = v_a_3794_;
v___y_3849_ = v_a_3795_;
goto v___jp_3838_;
}
else
{
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_he_3784_);
lean_dec_ref(v_e_3783_);
lean_dec_ref(v_c_3782_);
return v___x_3863_;
}
}
else
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
lean_dec_ref(v_a_3792_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_a_3789_);
lean_dec_ref(v_a_3788_);
lean_dec(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_he_3784_);
lean_dec_ref(v_e_3783_);
lean_dec_ref(v_c_3782_);
v_a_3864_ = lean_ctor_get(v___x_3861_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3861_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3866_ = v___x_3861_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v___x_3861_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
v___jp_3797_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3814_, 0, v___y_3800_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*1, v___y_3813_);
v___x_3815_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3812_, v___y_3811_, v___x_3814_, v___y_3809_, v___y_3807_, v___y_3806_, v___y_3801_, v___y_3808_, v___y_3798_, v___y_3804_, v___y_3802_, v___y_3810_, v___y_3805_, v___y_3799_, v___y_3803_);
return v___x_3815_;
}
v___jp_3816_:
{
uint8_t v_kind_3829_; 
v_kind_3829_ = lean_ctor_get_uint8(v_c_3782_, sizeof(void*)*5);
if (v_kind_3829_ == 1)
{
lean_object* v_u_3830_; lean_object* v_v_3831_; lean_object* v_k_3832_; uint8_t v___x_3833_; 
v_u_3830_ = lean_ctor_get(v_c_3782_, 0);
lean_inc(v_u_3830_);
v_v_3831_ = lean_ctor_get(v_c_3782_, 1);
lean_inc(v_v_3831_);
v_k_3832_ = lean_ctor_get(v_c_3782_, 2);
lean_inc(v_k_3832_);
lean_dec_ref(v_c_3782_);
v___x_3833_ = 1;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3827_;
v___y_3800_ = v_k_3832_;
v___y_3801_ = v___y_3820_;
v___y_3802_ = v___y_3824_;
v___y_3803_ = v___y_3828_;
v___y_3804_ = v___y_3823_;
v___y_3805_ = v___y_3826_;
v___y_3806_ = v___y_3819_;
v___y_3807_ = v___y_3818_;
v___y_3808_ = v___y_3821_;
v___y_3809_ = v_h_3817_;
v___y_3810_ = v___y_3825_;
v___y_3811_ = v_v_3831_;
v___y_3812_ = v_u_3830_;
v___y_3813_ = v___x_3833_;
goto v___jp_3797_;
}
else
{
lean_object* v_u_3834_; lean_object* v_v_3835_; lean_object* v_k_3836_; uint8_t v___x_3837_; 
v_u_3834_ = lean_ctor_get(v_c_3782_, 0);
lean_inc(v_u_3834_);
v_v_3835_ = lean_ctor_get(v_c_3782_, 1);
lean_inc(v_v_3835_);
v_k_3836_ = lean_ctor_get(v_c_3782_, 2);
lean_inc(v_k_3836_);
lean_dec_ref(v_c_3782_);
v___x_3837_ = 0;
v___y_3798_ = v___y_3822_;
v___y_3799_ = v___y_3827_;
v___y_3800_ = v_k_3836_;
v___y_3801_ = v___y_3820_;
v___y_3802_ = v___y_3824_;
v___y_3803_ = v___y_3828_;
v___y_3804_ = v___y_3823_;
v___y_3805_ = v___y_3826_;
v___y_3806_ = v___y_3819_;
v___y_3807_ = v___y_3818_;
v___y_3808_ = v___y_3821_;
v___y_3809_ = v_h_3817_;
v___y_3810_ = v___y_3825_;
v___y_3811_ = v_v_3835_;
v___y_3812_ = v_u_3834_;
v___y_3813_ = v___x_3837_;
goto v___jp_3797_;
}
}
v___jp_3838_:
{
lean_object* v_h_x3f_3850_; 
v_h_x3f_3850_ = lean_ctor_get(v_c_3782_, 4);
if (lean_obj_tag(v_h_x3f_3850_) == 1)
{
lean_object* v_e_3851_; lean_object* v_val_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_e_3851_ = lean_ctor_get(v_c_3782_, 3);
v_val_3852_ = lean_ctor_get(v_h_x3f_3850_, 0);
v___x_3853_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3783_);
v___x_3854_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3783_, v_he_3784_);
lean_inc(v_val_3852_);
lean_inc_ref(v_e_3851_);
v___x_3855_ = l_Lean_mkApp4(v___x_3853_, v_e_3783_, v_e_3851_, v_val_3852_, v___x_3854_);
v_h_3817_ = v___x_3855_;
v___y_3818_ = v___y_3839_;
v___y_3819_ = v___y_3840_;
v___y_3820_ = v___y_3841_;
v___y_3821_ = v___y_3842_;
v___y_3822_ = v___y_3843_;
v___y_3823_ = v___y_3844_;
v___y_3824_ = v___y_3845_;
v___y_3825_ = v___y_3846_;
v___y_3826_ = v___y_3847_;
v___y_3827_ = v___y_3848_;
v___y_3828_ = v___y_3849_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3856_; 
v___x_3856_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3783_, v_he_3784_);
v_h_3817_ = v___x_3856_;
v___y_3818_ = v___y_3839_;
v___y_3819_ = v___y_3840_;
v___y_3820_ = v___y_3841_;
v___y_3821_ = v___y_3842_;
v___y_3822_ = v___y_3843_;
v___y_3823_ = v___y_3844_;
v___y_3824_ = v___y_3845_;
v___y_3825_ = v___y_3846_;
v___y_3826_ = v___y_3847_;
v___y_3827_ = v___y_3848_;
v___y_3828_ = v___y_3849_;
goto v___jp_3816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3872_, lean_object* v_e_3873_, lean_object* v_he_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3872_, v_e_3873_, v_he_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v_res_3887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_box(0);
v___x_3895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3896_ = l_Lean_mkConst(v___x_3895_, v___x_3894_);
return v___x_3896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_unsigned_to_nat(1u);
v___x_3898_ = lean_nat_to_int(v___x_3897_);
return v___x_3898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = lean_unsigned_to_nat(0u);
v___x_3900_ = lean_nat_to_int(v___x_3899_);
return v___x_3900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = l_Lean_Level_ofNat(v___x_3906_);
return v___x_3907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3908_ = lean_box(0);
v___x_3909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v___x_3908_);
return v___x_3910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3912_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3913_ = l_Lean_Expr_const___override(v___x_3912_, v___x_3911_);
return v___x_3913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_box(0);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3919_ = l_Lean_Expr_const___override(v___x_3918_, v___x_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3924_ = lean_box(0);
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3926_ = l_Lean_Expr_const___override(v___x_3925_, v___x_3924_);
return v___x_3926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_box(0);
v___x_3964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3965_ = l_Lean_mkConst(v___x_3964_, v___x_3963_);
return v___x_3965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3968_ = l_Lean_stringToMessageData(v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3969_, lean_object* v_e_3970_, lean_object* v_he_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v_k_x27_3987_; lean_object* v_h_3988_; uint8_t v_strict_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; uint8_t v___y_4045_; lean_object* v___x_4091_; 
v___x_4091_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4411_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4094_ = v___x_4091_;
v_isShared_4095_ = v_isSharedCheck_4411_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4091_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4411_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; uint8_t v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; uint8_t v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v_h_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; lean_object* v___y_4381_; uint8_t v___x_4389_; 
v___x_4389_ = lean_unbox(v_a_4092_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4392_; 
lean_dec(v_a_4092_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_he_3971_);
lean_dec_ref(v_e_3970_);
lean_dec_ref(v_c_3969_);
v___x_4390_ = lean_box(0);
if (v_isShared_4095_ == 0)
{
lean_ctor_set(v___x_4094_, 0, v___x_4390_);
v___x_4392_ = v___x_4094_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v_a_4396_; uint8_t v___x_4397_; 
lean_del_object(v___x_4094_);
v___x_4394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4395_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4394_, v_a_3981_);
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref(v___x_4395_);
v___x_4397_ = lean_unbox(v_a_4396_);
lean_dec(v_a_4396_);
if (v___x_4397_ == 0)
{
v___y_4371_ = v_a_3972_;
v___y_4372_ = v_a_3973_;
v___y_4373_ = v_a_3974_;
v___y_4374_ = v_a_3975_;
v___y_4375_ = v_a_3976_;
v___y_4376_ = v_a_3977_;
v___y_4377_ = v_a_3978_;
v___y_4378_ = v_a_3979_;
v___y_4379_ = v_a_3980_;
v___y_4380_ = v_a_3981_;
v___y_4381_ = v_a_3982_;
goto v___jp_4370_;
}
else
{
lean_object* v___x_4398_; 
v___x_4398_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3969_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref(v___x_4398_);
v___x_4400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
lean_ctor_set(v___x_4401_, 1, v_a_4399_);
v___x_4402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v___x_4394_, v___x_4401_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref(v___x_4402_);
v___y_4371_ = v_a_3972_;
v___y_4372_ = v_a_3973_;
v___y_4373_ = v_a_3974_;
v___y_4374_ = v_a_3975_;
v___y_4375_ = v_a_3976_;
v___y_4376_ = v_a_3977_;
v___y_4377_ = v_a_3978_;
v___y_4378_ = v_a_3979_;
v___y_4379_ = v_a_3980_;
v___y_4380_ = v_a_3981_;
v___y_4381_ = v_a_3982_;
goto v___jp_4370_;
}
else
{
lean_dec(v_a_4092_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_he_3971_);
lean_dec_ref(v_e_3970_);
lean_dec_ref(v_c_3969_);
return v___x_4402_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_a_4092_);
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_he_3971_);
lean_dec_ref(v_e_3970_);
lean_dec_ref(v_c_3969_);
v_a_4403_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4398_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4398_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
v___jp_4096_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_4117_);
v___x_4119_ = l_Lean_mkApp6(v___y_4116_, v___y_4097_, v___y_4111_, v___y_4108_, v___y_4117_, v___x_4118_, v___y_4102_);
if (v___y_4105_ == 0)
{
uint8_t v___x_4120_; 
v___x_4120_ = lean_unbox(v_a_4092_);
lean_dec(v_a_4092_);
v___y_4028_ = v___y_4098_;
v___y_4029_ = v___y_4099_;
v___y_4030_ = v___y_4100_;
v___y_4031_ = v___y_4101_;
v___y_4032_ = v___y_4103_;
v___y_4033_ = v___x_4119_;
v___y_4034_ = v___y_4104_;
v___y_4035_ = v___y_4106_;
v___y_4036_ = v___y_4107_;
v___y_4037_ = v___x_4118_;
v___y_4038_ = v___y_4110_;
v___y_4039_ = v___y_4109_;
v___y_4040_ = v___y_4112_;
v___y_4041_ = v___y_4117_;
v___y_4042_ = v___y_4113_;
v___y_4043_ = v___y_4114_;
v___y_4044_ = v___y_4115_;
v___y_4045_ = v___x_4120_;
goto v___jp_4027_;
}
else
{
uint8_t v___x_4121_; 
lean_dec(v_a_4092_);
v___x_4121_ = 0;
v___y_4028_ = v___y_4098_;
v___y_4029_ = v___y_4099_;
v___y_4030_ = v___y_4100_;
v___y_4031_ = v___y_4101_;
v___y_4032_ = v___y_4103_;
v___y_4033_ = v___x_4119_;
v___y_4034_ = v___y_4104_;
v___y_4035_ = v___y_4106_;
v___y_4036_ = v___y_4107_;
v___y_4037_ = v___x_4118_;
v___y_4038_ = v___y_4110_;
v___y_4039_ = v___y_4109_;
v___y_4040_ = v___y_4112_;
v___y_4041_ = v___y_4117_;
v___y_4042_ = v___y_4113_;
v___y_4043_ = v___y_4114_;
v___y_4044_ = v___y_4115_;
v___y_4045_ = v___x_4121_;
goto v___jp_4027_;
}
}
v___jp_4122_:
{
lean_object* v___x_4143_; uint8_t v___x_4144_; 
v___x_4143_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4144_ = lean_int_dec_le(v___x_4143_, v___y_4129_);
if (v___x_4144_ == 0)
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4148_ = lean_int_neg(v___y_4129_);
v___x_4149_ = l_Int_toNat(v___x_4148_);
lean_dec(v___x_4148_);
v___x_4150_ = l_Lean_instToExprInt_mkNat(v___x_4149_);
v___x_4151_ = l_Lean_mkApp3(v___x_4145_, v___x_4146_, v___x_4147_, v___x_4150_);
v___y_4097_ = v___y_4123_;
v___y_4098_ = v___y_4124_;
v___y_4099_ = v___y_4125_;
v___y_4100_ = v___y_4126_;
v___y_4101_ = v___y_4127_;
v___y_4102_ = v___y_4128_;
v___y_4103_ = v___y_4129_;
v___y_4104_ = v___y_4130_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___y_4133_;
v___y_4108_ = v___y_4142_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4141_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___x_4151_;
goto v___jp_4096_;
}
else
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4152_ = l_Int_toNat(v___y_4129_);
v___x_4153_ = l_Lean_instToExprInt_mkNat(v___x_4152_);
v___y_4097_ = v___y_4123_;
v___y_4098_ = v___y_4124_;
v___y_4099_ = v___y_4125_;
v___y_4100_ = v___y_4126_;
v___y_4101_ = v___y_4127_;
v___y_4102_ = v___y_4128_;
v___y_4103_ = v___y_4129_;
v___y_4104_ = v___y_4130_;
v___y_4105_ = v___y_4131_;
v___y_4106_ = v___y_4132_;
v___y_4107_ = v___y_4133_;
v___y_4108_ = v___y_4142_;
v___y_4109_ = v___y_4134_;
v___y_4110_ = v___y_4135_;
v___y_4111_ = v___y_4136_;
v___y_4112_ = v___y_4137_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___y_4139_;
v___y_4115_ = v___y_4141_;
v___y_4116_ = v___y_4140_;
v___y_4117_ = v___x_4153_;
goto v___jp_4096_;
}
}
v___jp_4154_:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4171_, v___y_4157_, v___y_4167_, v___y_4163_, v___y_4160_, v___y_4162_, v___y_4169_, v___y_4155_, v___y_4164_, v___y_4165_, v___y_4170_, v___y_4158_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4174_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_a_4173_);
lean_dec_ref(v___x_4172_);
v___x_4174_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4156_, v___y_4157_, v___y_4167_, v___y_4163_, v___y_4160_, v___y_4162_, v___y_4169_, v___y_4155_, v___y_4164_, v___y_4165_, v___y_4170_, v___y_4158_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref(v___x_4174_);
v___x_4176_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4168_, v___y_4157_, v___y_4167_, v___y_4163_, v___y_4160_, v___y_4162_, v___y_4169_, v___y_4155_, v___y_4164_, v___y_4165_, v___y_4170_, v___y_4158_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; uint8_t v___x_4180_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = lean_int_neg(v___y_4166_);
v___x_4179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4180_ = lean_int_dec_le(v___x_4179_, v___y_4166_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_dec(v___y_4166_);
v___x_4181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4184_ = l_Int_toNat(v___x_4178_);
v___x_4185_ = l_Lean_instToExprInt_mkNat(v___x_4184_);
v___x_4186_ = l_Lean_mkApp3(v___x_4181_, v___x_4182_, v___x_4183_, v___x_4185_);
v___y_4123_ = v_a_4175_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___x_4178_;
v___y_4130_ = v___y_4160_;
v___y_4131_ = v___y_4161_;
v___y_4132_ = v___y_4162_;
v___y_4133_ = v___y_4163_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4164_;
v___y_4136_ = v_a_4177_;
v___y_4137_ = v___y_4167_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v_a_4173_;
v___y_4141_ = v___y_4170_;
v___y_4142_ = v___x_4186_;
goto v___jp_4122_;
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = l_Int_toNat(v___y_4166_);
lean_dec(v___y_4166_);
v___x_4188_ = l_Lean_instToExprInt_mkNat(v___x_4187_);
v___y_4123_ = v_a_4175_;
v___y_4124_ = v___y_4155_;
v___y_4125_ = v___y_4156_;
v___y_4126_ = v___y_4157_;
v___y_4127_ = v___y_4158_;
v___y_4128_ = v___y_4159_;
v___y_4129_ = v___x_4178_;
v___y_4130_ = v___y_4160_;
v___y_4131_ = v___y_4161_;
v___y_4132_ = v___y_4162_;
v___y_4133_ = v___y_4163_;
v___y_4134_ = v___y_4165_;
v___y_4135_ = v___y_4164_;
v___y_4136_ = v_a_4177_;
v___y_4137_ = v___y_4167_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4169_;
v___y_4140_ = v_a_4173_;
v___y_4141_ = v___y_4170_;
v___y_4142_ = v___x_4188_;
goto v___jp_4122_;
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec(v_a_4175_);
lean_dec(v_a_4173_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v_a_4092_);
v_a_4189_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4176_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4176_);
v___x_4191_ = lean_box(0);
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
v_resetjp_4190_:
{
lean_object* v___x_4194_; 
if (v_isShared_4192_ == 0)
{
v___x_4194_ = v___x_4191_;
goto v_reusejp_4193_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
v___x_4194_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4193_;
}
v_reusejp_4193_:
{
return v___x_4194_;
}
}
}
}
else
{
lean_object* v_a_4197_; lean_object* v___x_4199_; uint8_t v_isShared_4200_; uint8_t v_isSharedCheck_4204_; 
lean_dec(v_a_4173_);
lean_dec_ref(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v_a_4092_);
v_a_4197_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4199_ = v___x_4174_;
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
else
{
lean_inc(v_a_4197_);
lean_dec(v___x_4174_);
v___x_4199_ = lean_box(0);
v_isShared_4200_ = v_isSharedCheck_4204_;
goto v_resetjp_4198_;
}
v_resetjp_4198_:
{
lean_object* v___x_4202_; 
if (v_isShared_4200_ == 0)
{
v___x_4202_ = v___x_4199_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec_ref(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec(v_a_4092_);
v_a_4205_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4172_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4172_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
}
v___jp_4213_:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Lean_Meta_Grind_Order_isRing(v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; uint8_t v___x_4228_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = lean_unbox(v_a_4227_);
if (v___x_4228_ == 0)
{
uint8_t v_kind_4229_; 
v_kind_4229_ = lean_ctor_get_uint8(v_c_3969_, sizeof(void*)*5);
if (v_kind_4229_ == 1)
{
lean_object* v_u_4230_; lean_object* v_v_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec(v_a_4092_);
v_u_4230_ = lean_ctor_get(v_c_3969_, 0);
lean_inc(v_u_4230_);
v_v_4231_ = lean_ctor_get(v_c_3969_, 1);
lean_inc(v_v_4231_);
lean_dec_ref(v_c_3969_);
v___x_4232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4233_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4232_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref(v___x_4233_);
v___x_4235_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4230_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4231_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; lean_object* v___x_4243_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref(v___x_4237_);
v___x_4239_ = l_Lean_mkApp3(v_a_4234_, v_a_4236_, v_a_4238_, v_h_4214_);
v___x_4240_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4241_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
v___x_4242_ = lean_unbox(v_a_4227_);
lean_dec(v_a_4227_);
lean_ctor_set_uint8(v___x_4241_, sizeof(void*)*1, v___x_4242_);
v___x_4243_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4231_, v_u_4230_, v___x_4241_, v___x_4239_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
return v___x_4243_;
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v_a_4236_);
lean_dec(v_a_4234_);
lean_dec(v_v_4231_);
lean_dec(v_u_4230_);
lean_dec(v_a_4227_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4244_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4237_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4237_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_a_4234_);
lean_dec(v_v_4231_);
lean_dec(v_u_4230_);
lean_dec(v_a_4227_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4252_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4235_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4235_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v_v_4231_);
lean_dec(v_u_4230_);
lean_dec(v_a_4227_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4260_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4233_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4233_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v_u_4268_; lean_object* v_v_4269_; lean_object* v___x_4270_; 
lean_dec(v_a_4227_);
v_u_4268_ = lean_ctor_get(v_c_3969_, 0);
lean_inc(v_u_4268_);
v_v_4269_ = lean_ctor_get(v_c_3969_, 1);
lean_inc(v_v_4269_);
lean_dec_ref(v_c_3969_);
v___x_4270_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; uint8_t v___x_4272_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_a_4271_);
lean_dec_ref(v___x_4270_);
v___x_4272_ = lean_unbox(v_a_4271_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; 
lean_dec(v_a_4092_);
v___x_4273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4274_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4273_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4276_; 
v_a_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v___x_4274_);
v___x_4276_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4268_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v_a_4277_; lean_object* v___x_4278_; 
v_a_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc(v_a_4277_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4269_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v_a_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; 
v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_a_4279_);
lean_dec_ref(v___x_4278_);
v___x_4280_ = l_Lean_mkApp3(v_a_4275_, v_a_4277_, v_a_4279_, v_h_4214_);
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4282_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
v___x_4283_ = lean_unbox(v_a_4271_);
lean_dec(v_a_4271_);
lean_ctor_set_uint8(v___x_4282_, sizeof(void*)*1, v___x_4283_);
v___x_4284_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4269_, v_u_4268_, v___x_4282_, v___x_4280_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
return v___x_4284_;
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v_a_4277_);
lean_dec(v_a_4275_);
lean_dec(v_a_4271_);
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4285_ = lean_ctor_get(v___x_4278_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4278_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4278_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4278_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec(v_a_4275_);
lean_dec(v_a_4271_);
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4293_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4276_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4276_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
else
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4308_; 
lean_dec(v_a_4271_);
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
v_a_4301_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4308_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4308_ == 0)
{
v___x_4303_ = v___x_4274_;
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4274_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4308_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
lean_object* v___x_4306_; 
if (v_isShared_4304_ == 0)
{
v___x_4306_ = v___x_4303_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v_a_4301_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
}
}
else
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
lean_dec(v_a_4271_);
v___x_4309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4310_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4309_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4310_);
v___x_4312_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4268_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4269_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = l_Lean_mkApp3(v_a_4311_, v_a_4313_, v_a_4315_, v_h_4214_);
v___x_4317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4318_, 0, v___x_4317_);
v___x_4319_ = lean_unbox(v_a_4092_);
lean_dec(v_a_4092_);
lean_ctor_set_uint8(v___x_4318_, sizeof(void*)*1, v___x_4319_);
v___x_4320_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4269_, v_u_4268_, v___x_4318_, v___x_4316_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
return v___x_4320_;
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_a_4313_);
lean_dec(v_a_4311_);
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
lean_dec(v_a_4092_);
v_a_4321_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4314_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4314_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
else
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
lean_dec(v_a_4311_);
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
lean_dec(v_a_4092_);
v_a_4329_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4312_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4312_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
lean_dec(v_a_4092_);
v_a_4337_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4310_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4310_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
return v___x_4342_;
}
}
}
}
}
else
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4352_; 
lean_dec(v_v_4269_);
lean_dec(v_u_4268_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
lean_dec(v_a_4092_);
v_a_4345_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4352_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4352_ == 0)
{
v___x_4347_ = v___x_4270_;
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4270_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4352_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
lean_object* v___x_4350_; 
if (v_isShared_4348_ == 0)
{
v___x_4350_ = v___x_4347_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v_a_4345_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
}
}
}
else
{
uint8_t v_kind_4353_; 
lean_dec(v_a_4227_);
v_kind_4353_ = lean_ctor_get_uint8(v_c_3969_, sizeof(void*)*5);
if (v_kind_4353_ == 1)
{
lean_object* v_u_4354_; lean_object* v_v_4355_; lean_object* v_k_4356_; lean_object* v___x_4357_; 
v_u_4354_ = lean_ctor_get(v_c_3969_, 0);
lean_inc(v_u_4354_);
v_v_4355_ = lean_ctor_get(v_c_3969_, 1);
lean_inc(v_v_4355_);
v_k_4356_ = lean_ctor_get(v_c_3969_, 2);
lean_inc(v_k_4356_);
lean_dec_ref(v_c_3969_);
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4155_ = v___y_4221_;
v___y_4156_ = v_u_4354_;
v___y_4157_ = v___y_4215_;
v___y_4158_ = v___y_4225_;
v___y_4159_ = v_h_4214_;
v___y_4160_ = v___y_4218_;
v___y_4161_ = v_kind_4353_;
v___y_4162_ = v___y_4219_;
v___y_4163_ = v___y_4217_;
v___y_4164_ = v___y_4222_;
v___y_4165_ = v___y_4223_;
v___y_4166_ = v_k_4356_;
v___y_4167_ = v___y_4216_;
v___y_4168_ = v_v_4355_;
v___y_4169_ = v___y_4220_;
v___y_4170_ = v___y_4224_;
v___y_4171_ = v___x_4357_;
goto v___jp_4154_;
}
else
{
lean_object* v_u_4358_; lean_object* v_v_4359_; lean_object* v_k_4360_; lean_object* v___x_4361_; 
v_u_4358_ = lean_ctor_get(v_c_3969_, 0);
lean_inc(v_u_4358_);
v_v_4359_ = lean_ctor_get(v_c_3969_, 1);
lean_inc(v_v_4359_);
v_k_4360_ = lean_ctor_get(v_c_3969_, 2);
lean_inc(v_k_4360_);
lean_dec_ref(v_c_3969_);
v___x_4361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4155_ = v___y_4221_;
v___y_4156_ = v_u_4358_;
v___y_4157_ = v___y_4215_;
v___y_4158_ = v___y_4225_;
v___y_4159_ = v_h_4214_;
v___y_4160_ = v___y_4218_;
v___y_4161_ = v_kind_4353_;
v___y_4162_ = v___y_4219_;
v___y_4163_ = v___y_4217_;
v___y_4164_ = v___y_4222_;
v___y_4165_ = v___y_4223_;
v___y_4166_ = v_k_4360_;
v___y_4167_ = v___y_4216_;
v___y_4168_ = v_v_4359_;
v___y_4169_ = v___y_4220_;
v___y_4170_ = v___y_4224_;
v___y_4171_ = v___x_4361_;
goto v___jp_4154_;
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_h_4214_);
lean_dec(v_a_4092_);
lean_dec_ref(v_c_3969_);
v_a_4362_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4226_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4226_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
v___jp_4370_:
{
lean_object* v_h_x3f_4382_; 
v_h_x3f_4382_ = lean_ctor_get(v_c_3969_, 4);
if (lean_obj_tag(v_h_x3f_4382_) == 1)
{
lean_object* v_e_4383_; lean_object* v_val_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_e_4383_ = lean_ctor_get(v_c_3969_, 3);
v_val_4384_ = lean_ctor_get(v_h_x3f_4382_, 0);
v___x_4385_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3970_);
v___x_4386_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3970_, v_he_3971_);
lean_inc(v_val_4384_);
lean_inc_ref(v_e_4383_);
v___x_4387_ = l_Lean_mkApp4(v___x_4385_, v_e_3970_, v_e_4383_, v_val_4384_, v___x_4386_);
v_h_4214_ = v___x_4387_;
v___y_4215_ = v___y_4371_;
v___y_4216_ = v___y_4372_;
v___y_4217_ = v___y_4373_;
v___y_4218_ = v___y_4374_;
v___y_4219_ = v___y_4375_;
v___y_4220_ = v___y_4376_;
v___y_4221_ = v___y_4377_;
v___y_4222_ = v___y_4378_;
v___y_4223_ = v___y_4379_;
v___y_4224_ = v___y_4380_;
v___y_4225_ = v___y_4381_;
goto v___jp_4213_;
}
else
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3970_, v_he_3971_);
v_h_4214_ = v___x_4388_;
v___y_4215_ = v___y_4371_;
v___y_4216_ = v___y_4372_;
v___y_4217_ = v___y_4373_;
v___y_4218_ = v___y_4374_;
v___y_4219_ = v___y_4375_;
v___y_4220_ = v___y_4376_;
v___y_4221_ = v___y_4377_;
v___y_4222_ = v___y_4378_;
v___y_4223_ = v___y_4379_;
v___y_4224_ = v___y_4380_;
v___y_4225_ = v___y_4381_;
goto v___jp_4213_;
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_a_3982_);
lean_dec_ref(v_a_3981_);
lean_dec(v_a_3980_);
lean_dec_ref(v_a_3979_);
lean_dec(v_a_3978_);
lean_dec_ref(v_a_3977_);
lean_dec(v_a_3976_);
lean_dec_ref(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec(v_a_3972_);
lean_dec_ref(v_he_3971_);
lean_dec_ref(v_e_3970_);
lean_dec_ref(v_c_3969_);
v_a_4412_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4091_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4091_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
v___jp_3984_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4001_, 0, v_k_x27_3987_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*1, v_strict_3989_);
v___x_4002_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3986_, v___y_3985_, v___x_4001_, v_h_3988_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
return v___x_4002_;
}
v___jp_4003_:
{
lean_object* v___x_4025_; uint8_t v___x_4026_; 
v___x_4025_ = l_Lean_mkApp6(v___y_4014_, v___y_4009_, v___y_4008_, v___y_4020_, v___y_4024_, v___y_4015_, v___y_4010_);
v___x_4026_ = 0;
v___y_3985_ = v___y_4005_;
v___y_3986_ = v___y_4021_;
v_k_x27_3987_ = v___y_4018_;
v_h_3988_ = v___x_4025_;
v_strict_3989_ = v___x_4026_;
v___y_3990_ = v___y_4006_;
v___y_3991_ = v___y_4019_;
v___y_3992_ = v___y_4013_;
v___y_3993_ = v___y_4011_;
v___y_3994_ = v___y_4012_;
v___y_3995_ = v___y_4022_;
v___y_3996_ = v___y_4004_;
v___y_3997_ = v___y_4017_;
v___y_3998_ = v___y_4016_;
v___y_3999_ = v___y_4023_;
v___y_4000_ = v___y_4007_;
goto v___jp_3984_;
}
v___jp_4027_:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Meta_Grind_Order_isInt(v___y_4030_, v___y_4040_, v___y_4036_, v___y_4034_, v___y_4035_, v___y_4043_, v___y_4028_, v___y_4038_, v___y_4039_, v___y_4044_, v___y_4031_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; uint8_t v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref(v___x_4046_);
v___x_4048_ = lean_unbox(v_a_4047_);
lean_dec(v_a_4047_);
if (v___x_4048_ == 0)
{
lean_dec_ref(v___y_4041_);
lean_dec_ref(v___y_4037_);
v___y_3985_ = v___y_4029_;
v___y_3986_ = v___y_4042_;
v_k_x27_3987_ = v___y_4032_;
v_h_3988_ = v___y_4033_;
v_strict_3989_ = v___y_4045_;
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___y_4040_;
v___y_3992_ = v___y_4036_;
v___y_3993_ = v___y_4034_;
v___y_3994_ = v___y_4035_;
v___y_3995_ = v___y_4043_;
v___y_3996_ = v___y_4028_;
v___y_3997_ = v___y_4038_;
v___y_3998_ = v___y_4039_;
v___y_3999_ = v___y_4044_;
v___y_4000_ = v___y_4031_;
goto v___jp_3984_;
}
else
{
if (v___y_4045_ == 0)
{
lean_dec_ref(v___y_4041_);
lean_dec_ref(v___y_4037_);
v___y_3985_ = v___y_4029_;
v___y_3986_ = v___y_4042_;
v_k_x27_3987_ = v___y_4032_;
v_h_3988_ = v___y_4033_;
v_strict_3989_ = v___y_4045_;
v___y_3990_ = v___y_4030_;
v___y_3991_ = v___y_4040_;
v___y_3992_ = v___y_4036_;
v___y_3993_ = v___y_4034_;
v___y_3994_ = v___y_4035_;
v___y_3995_ = v___y_4043_;
v___y_3996_ = v___y_4028_;
v___y_3997_ = v___y_4038_;
v___y_3998_ = v___y_4039_;
v___y_3999_ = v___y_4044_;
v___y_4000_ = v___y_4031_;
goto v___jp_3984_;
}
else
{
lean_object* v___x_4049_; 
v___x_4049_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4042_, v___y_4030_, v___y_4040_, v___y_4036_, v___y_4034_, v___y_4035_, v___y_4043_, v___y_4028_, v___y_4038_, v___y_4039_, v___y_4044_, v___y_4031_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref(v___x_4049_);
v___x_4051_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4029_, v___y_4030_, v___y_4040_, v___y_4036_, v___y_4034_, v___y_4035_, v___y_4043_, v___y_4028_, v___y_4038_, v___y_4039_, v___y_4044_, v___y_4031_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; uint8_t v___x_4057_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref(v___x_4051_);
v___x_4053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_4054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_4055_ = lean_int_sub(v___y_4032_, v___x_4054_);
lean_dec(v___y_4032_);
v___x_4056_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4057_ = lean_int_dec_le(v___x_4056_, v___x_4055_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4059_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4061_ = lean_int_neg(v___x_4055_);
v___x_4062_ = l_Int_toNat(v___x_4061_);
lean_dec(v___x_4061_);
v___x_4063_ = l_Lean_instToExprInt_mkNat(v___x_4062_);
v___x_4064_ = l_Lean_mkApp3(v___x_4058_, v___x_4059_, v___x_4060_, v___x_4063_);
v___y_4004_ = v___y_4028_;
v___y_4005_ = v___y_4029_;
v___y_4006_ = v___y_4030_;
v___y_4007_ = v___y_4031_;
v___y_4008_ = v_a_4052_;
v___y_4009_ = v_a_4050_;
v___y_4010_ = v___y_4033_;
v___y_4011_ = v___y_4034_;
v___y_4012_ = v___y_4035_;
v___y_4013_ = v___y_4036_;
v___y_4014_ = v___x_4053_;
v___y_4015_ = v___y_4037_;
v___y_4016_ = v___y_4039_;
v___y_4017_ = v___y_4038_;
v___y_4018_ = v___x_4055_;
v___y_4019_ = v___y_4040_;
v___y_4020_ = v___y_4041_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4044_;
v___y_4024_ = v___x_4064_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = l_Int_toNat(v___x_4055_);
v___x_4066_ = l_Lean_instToExprInt_mkNat(v___x_4065_);
v___y_4004_ = v___y_4028_;
v___y_4005_ = v___y_4029_;
v___y_4006_ = v___y_4030_;
v___y_4007_ = v___y_4031_;
v___y_4008_ = v_a_4052_;
v___y_4009_ = v_a_4050_;
v___y_4010_ = v___y_4033_;
v___y_4011_ = v___y_4034_;
v___y_4012_ = v___y_4035_;
v___y_4013_ = v___y_4036_;
v___y_4014_ = v___x_4053_;
v___y_4015_ = v___y_4037_;
v___y_4016_ = v___y_4039_;
v___y_4017_ = v___y_4038_;
v___y_4018_ = v___x_4055_;
v___y_4019_ = v___y_4040_;
v___y_4020_ = v___y_4041_;
v___y_4021_ = v___y_4042_;
v___y_4022_ = v___y_4043_;
v___y_4023_ = v___y_4044_;
v___y_4024_ = v___x_4066_;
goto v___jp_4003_;
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec(v_a_4050_);
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec(v___y_4028_);
v_a_4067_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4051_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4051_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec(v___y_4028_);
v_a_4075_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4049_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4049_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec(v___y_4028_);
v_a_4083_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4046_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4046_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4420_, lean_object* v_e_4421_, lean_object* v_he_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4420_, v_e_4421_, v_he_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4436_, lean_object* v_a_4437_, lean_object* v_a_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4437_, v_a_4438_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4450_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4443_ = v___x_4440_;
v_isShared_4444_ = v_isSharedCheck_4450_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4440_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4450_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v_exprToStructId_4445_; lean_object* v___x_4446_; lean_object* v___x_4448_; 
v_exprToStructId_4445_ = lean_ctor_get(v_a_4441_, 2);
lean_inc_ref(v_exprToStructId_4445_);
lean_dec(v_a_4441_);
v___x_4446_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4445_, v_e_4436_);
if (v_isShared_4444_ == 0)
{
lean_ctor_set(v___x_4443_, 0, v___x_4446_);
v___x_4448_ = v___x_4443_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
v_a_4451_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4440_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4440_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4459_, v_a_4460_, v_a_4461_);
lean_dec_ref(v_a_4461_);
lean_dec(v_a_4460_);
lean_dec_ref(v_e_4459_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_){
_start:
{
lean_object* v___x_4476_; 
v___x_4476_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4464_, v_a_4465_, v_a_4473_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec(v_a_4478_);
lean_dec_ref(v_e_4477_);
return v_res_4489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; 
v___x_4496_ = lean_box(0);
v___x_4497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4498_ = l_Lean_mkConst(v___x_4497_, v___x_4496_);
return v___x_4498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = lean_box(0);
v___x_4506_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4507_ = l_Lean_mkConst(v___x_4506_, v___x_4505_);
return v___x_4507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4508_, lean_object* v_e_x27_4509_, lean_object* v_he_x3f_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v___x_4522_; 
v___x_4522_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4509_, v_a_4511_, v_a_4519_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4613_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4525_ = v___x_4522_;
v_isShared_4526_ = v_isSharedCheck_4613_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4522_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4613_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
if (lean_obj_tag(v_a_4523_) == 1)
{
lean_object* v_val_4527_; lean_object* v___x_4528_; 
lean_del_object(v___x_4525_);
v_val_4527_ = lean_ctor_get(v_a_4523_, 0);
lean_inc(v_val_4527_);
lean_dec_ref(v_a_4523_);
v___x_4528_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_x27_4509_, v_val_4527_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4600_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4531_ = v___x_4528_;
v_isShared_4532_ = v_isSharedCheck_4600_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4600_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
if (lean_obj_tag(v_a_4529_) == 1)
{
lean_object* v_val_4533_; lean_object* v___x_4534_; 
lean_del_object(v___x_4531_);
v_val_4533_ = lean_ctor_get(v_a_4529_, 0);
lean_inc(v_val_4533_);
lean_dec_ref(v_a_4529_);
lean_inc_ref(v_e_4508_);
v___x_4534_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4508_, v_a_4511_, v_a_4515_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v_a_4535_; uint8_t v___x_4536_; 
v_a_4535_ = lean_ctor_get(v___x_4534_, 0);
lean_inc(v_a_4535_);
lean_dec_ref(v___x_4534_);
v___x_4536_ = lean_unbox(v_a_4535_);
lean_dec(v_a_4535_);
if (v___x_4536_ == 0)
{
lean_object* v___x_4537_; 
lean_inc_ref(v_e_4508_);
v___x_4537_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4508_, v_a_4511_, v_a_4515_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4563_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4540_ = v___x_4537_;
v_isShared_4541_ = v_isSharedCheck_4563_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4537_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4563_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
uint8_t v___x_4542_; 
v___x_4542_ = lean_unbox(v_a_4538_);
lean_dec(v_a_4538_);
if (v___x_4542_ == 0)
{
lean_object* v___x_4543_; lean_object* v___x_4545_; 
lean_dec(v_val_4533_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v___x_4543_ = lean_box(0);
if (v_isShared_4541_ == 0)
{
lean_ctor_set(v___x_4540_, 0, v___x_4543_);
v___x_4545_ = v___x_4540_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
else
{
lean_object* v___x_4547_; 
lean_del_object(v___x_4540_);
lean_inc(v_a_4520_);
lean_inc_ref(v_a_4519_);
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
lean_inc(v_a_4514_);
lean_inc_ref(v_a_4513_);
lean_inc(v_a_4512_);
lean_inc(v_a_4511_);
lean_inc_ref(v_e_4508_);
v___x_4547_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4508_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4547_) == 0)
{
if (lean_obj_tag(v_he_x3f_4510_) == 1)
{
lean_object* v_a_4548_; lean_object* v_val_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_a_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4548_);
lean_dec_ref(v___x_4547_);
v_val_4549_ = lean_ctor_get(v_he_x3f_4510_, 0);
lean_inc(v_val_4549_);
lean_dec_ref(v_he_x3f_4510_);
v___x_4550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4509_);
v___x_4551_ = l_Lean_mkApp4(v___x_4550_, v_e_4508_, v_e_x27_4509_, v_val_4549_, v_a_4548_);
v___x_4552_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4533_, v_e_x27_4509_, v___x_4551_, v_val_4527_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4552_;
}
else
{
lean_object* v_a_4553_; lean_object* v___x_4554_; 
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_4508_);
v_a_4553_ = lean_ctor_get(v___x_4547_, 0);
lean_inc(v_a_4553_);
lean_dec_ref(v___x_4547_);
v___x_4554_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4533_, v_e_x27_4509_, v_a_4553_, v_val_4527_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4554_;
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_val_4533_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4555_ = lean_ctor_get(v___x_4547_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4547_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4547_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4547_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec(v_val_4533_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4564_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4537_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4537_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v___x_4572_; 
lean_inc(v_a_4520_);
lean_inc_ref(v_a_4519_);
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
lean_inc(v_a_4514_);
lean_inc_ref(v_a_4513_);
lean_inc(v_a_4512_);
lean_inc(v_a_4511_);
lean_inc_ref(v_e_4508_);
v___x_4572_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4508_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
if (lean_obj_tag(v___x_4572_) == 0)
{
if (lean_obj_tag(v_he_x3f_4510_) == 1)
{
lean_object* v_a_4573_; lean_object* v_val_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4573_);
lean_dec_ref(v___x_4572_);
v_val_4574_ = lean_ctor_get(v_he_x3f_4510_, 0);
lean_inc(v_val_4574_);
lean_dec_ref(v_he_x3f_4510_);
v___x_4575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4509_);
v___x_4576_ = l_Lean_mkApp4(v___x_4575_, v_e_4508_, v_e_x27_4509_, v_val_4574_, v_a_4573_);
v___x_4577_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4533_, v_e_x27_4509_, v___x_4576_, v_val_4527_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4577_;
}
else
{
lean_object* v_a_4578_; lean_object* v___x_4579_; 
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_4508_);
v_a_4578_ = lean_ctor_get(v___x_4572_, 0);
lean_inc(v_a_4578_);
lean_dec_ref(v___x_4572_);
v___x_4579_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4533_, v_e_x27_4509_, v_a_4578_, v_val_4527_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
return v___x_4579_;
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec(v_val_4533_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4580_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4572_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4572_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
}
else
{
lean_object* v_a_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4595_; 
lean_dec(v_val_4533_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4588_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4590_ = v___x_4534_;
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_a_4588_);
lean_dec(v___x_4534_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4595_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4593_; 
if (v_isShared_4591_ == 0)
{
v___x_4593_ = v___x_4590_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4594_; 
v_reuseFailAlloc_4594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4594_, 0, v_a_4588_);
v___x_4593_ = v_reuseFailAlloc_4594_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
return v___x_4593_;
}
}
}
}
else
{
lean_object* v___x_4596_; lean_object* v___x_4598_; 
lean_dec(v_a_4529_);
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v___x_4596_ = lean_box(0);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 0, v___x_4596_);
v___x_4598_ = v___x_4531_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_val_4527_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4601_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4528_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4528_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_dec(v_a_4523_);
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v___x_4609_ = lean_box(0);
if (v_isShared_4526_ == 0)
{
lean_ctor_set(v___x_4525_, 0, v___x_4609_);
v___x_4611_ = v___x_4525_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_dec(v_a_4520_);
lean_dec_ref(v_a_4519_);
lean_dec(v_a_4518_);
lean_dec_ref(v_a_4517_);
lean_dec(v_a_4516_);
lean_dec_ref(v_a_4515_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec(v_he_x3f_4510_);
lean_dec_ref(v_e_x27_4509_);
lean_dec_ref(v_e_4508_);
v_a_4614_ = lean_ctor_get(v___x_4522_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4522_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4522_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4622_, lean_object* v_e_x27_4623_, lean_object* v_he_x3f_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4622_, v_e_x27_4623_, v_he_x3f_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4638_, v_a_4646_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v_termMap_4651_; lean_object* v___x_4652_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref(v___x_4649_);
v_termMap_4651_ = lean_ctor_get(v_a_4650_, 3);
lean_inc_ref(v_termMap_4651_);
lean_dec(v_a_4650_);
v___x_4652_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4651_, v_e_4637_);
if (lean_obj_tag(v___x_4652_) == 1)
{
lean_object* v_val_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4663_; 
v_val_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4663_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_val_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4663_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v_fst_4657_; lean_object* v_snd_4658_; lean_object* v___x_4660_; 
v_fst_4657_ = lean_ctor_get(v_val_4653_, 0);
lean_inc(v_fst_4657_);
v_snd_4658_ = lean_ctor_get(v_val_4653_, 1);
lean_inc(v_snd_4658_);
lean_dec(v_val_4653_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v_snd_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4662_; 
v_reuseFailAlloc_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_snd_4658_);
v___x_4660_ = v_reuseFailAlloc_4662_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; 
v___x_4661_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4637_, v_fst_4657_, v___x_4660_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4661_;
}
}
}
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_dec(v___x_4652_);
v___x_4664_ = lean_box(0);
lean_inc_ref(v_e_4637_);
v___x_4665_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4637_, v_e_4637_, v___x_4664_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4665_;
}
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec(v_a_4647_);
lean_dec_ref(v_a_4646_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec(v_a_4638_);
lean_dec_ref(v_e_4637_);
v_a_4666_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4649_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4649_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v_a_4684_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v___x_4699_; 
v___x_4699_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_);
return v_res_4712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___f_4720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4722_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4721_, v___f_4720_);
return v___x_4722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8____boxed(lean_object* v_a_4723_){
_start:
{
lean_object* v_res_4724_; 
v_res_4724_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
return v_res_4724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v___x_4737_; 
v___x_4737_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_, v_a_4735_);
return v___x_4737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v_res_4750_; 
v_res_4750_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
return v_res_4750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___f_4757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4758_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_));
v___x_4759_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4758_, v___f_4757_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8____boxed(lean_object* v_a_4760_){
_start:
{
lean_object* v_res_4761_; 
v_res_4761_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
return v_res_4761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_){
_start:
{
lean_object* v___x_4766_; 
v___x_4766_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4763_, v_a_4764_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4776_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4776_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4776_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4776_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4776_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v_termMap_4771_; lean_object* v___x_4772_; lean_object* v___x_4774_; 
v_termMap_4771_ = lean_ctor_get(v_a_4767_, 3);
lean_inc_ref(v_termMap_4771_);
lean_dec(v_a_4767_);
v___x_4772_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4771_, v_e_4762_);
if (v_isShared_4770_ == 0)
{
lean_ctor_set(v___x_4769_, 0, v___x_4772_);
v___x_4774_ = v___x_4769_;
goto v_reusejp_4773_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v___x_4772_);
v___x_4774_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4773_;
}
v_reusejp_4773_:
{
return v___x_4774_;
}
}
}
else
{
lean_object* v_a_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4784_; 
v_a_4777_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4779_ = v___x_4766_;
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
else
{
lean_inc(v_a_4777_);
lean_dec(v___x_4766_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4784_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
lean_object* v___x_4782_; 
if (v_isShared_4780_ == 0)
{
v___x_4782_ = v___x_4779_;
goto v_reusejp_4781_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4777_);
v___x_4782_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4781_;
}
v_reusejp_4781_:
{
return v___x_4782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4785_, v_a_4786_, v_a_4787_);
lean_dec_ref(v_a_4787_);
lean_dec(v_a_4786_);
lean_dec_ref(v_e_4785_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4790_, lean_object* v_a_4791_, lean_object* v_a_4792_, lean_object* v_a_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v___x_4802_; 
v___x_4802_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4790_, v_a_4791_, v_a_4799_);
return v___x_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_, lean_object* v_a_4810_, lean_object* v_a_4811_, lean_object* v_a_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_){
_start:
{
lean_object* v_res_4815_; 
v_res_4815_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_);
lean_dec(v_a_4813_);
lean_dec_ref(v_a_4812_);
lean_dec(v_a_4811_);
lean_dec_ref(v_a_4810_);
lean_dec(v_a_4809_);
lean_dec_ref(v_a_4808_);
lean_dec(v_a_4807_);
lean_dec_ref(v_a_4806_);
lean_dec(v_a_4805_);
lean_dec(v_a_4804_);
lean_dec_ref(v_e_4803_);
return v_res_4815_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = 0;
v___x_4841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4845_ = l_Lean_stringToMessageData(v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4846_, lean_object* v_b_4847_, lean_object* v_h_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_, lean_object* v_a_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; lean_object* v___x_4959_; 
v___x_4959_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4846_, v_a_4849_, v_a_4857_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_5003_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4962_ = v___x_4959_;
v_isShared_4963_ = v_isSharedCheck_5003_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4959_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_5003_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
if (lean_obj_tag(v_a_4960_) == 1)
{
lean_object* v_val_4964_; lean_object* v___x_4965_; 
lean_del_object(v___x_4962_);
v_val_4964_ = lean_ctor_get(v_a_4960_, 0);
lean_inc(v_val_4964_);
lean_dec_ref(v_a_4960_);
v___x_4965_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4847_, v_a_4849_, v_a_4857_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4990_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4968_ = v___x_4965_;
v_isShared_4969_ = v_isSharedCheck_4990_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4965_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4990_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
if (lean_obj_tag(v_a_4966_) == 1)
{
lean_object* v_val_4970_; uint8_t v___x_4971_; 
v_val_4970_ = lean_ctor_get(v_a_4966_, 0);
lean_inc(v_val_4970_);
lean_dec_ref(v_a_4966_);
v___x_4971_ = lean_nat_dec_eq(v_val_4964_, v_val_4970_);
lean_dec(v_val_4970_);
if (v___x_4971_ == 0)
{
lean_object* v___x_4972_; lean_object* v___x_4974_; 
lean_dec(v_val_4964_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v___x_4972_ = lean_box(0);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_4972_);
v___x_4974_ = v___x_4968_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v___x_4972_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
else
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v_a_4978_; uint8_t v___x_4979_; 
lean_del_object(v___x_4968_);
v___x_4976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4977_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4976_, v_a_4857_);
v_a_4978_ = lean_ctor_get(v___x_4977_, 0);
lean_inc(v_a_4978_);
lean_dec_ref(v___x_4977_);
v___x_4979_ = lean_unbox(v_a_4978_);
lean_dec(v_a_4978_);
if (v___x_4979_ == 0)
{
v___y_4861_ = v_val_4964_;
v___y_4862_ = v_a_4849_;
v___y_4863_ = v_a_4850_;
v___y_4864_ = v_a_4851_;
v___y_4865_ = v_a_4852_;
v___y_4866_ = v_a_4853_;
v___y_4867_ = v_a_4854_;
v___y_4868_ = v_a_4855_;
v___y_4869_ = v_a_4856_;
v___y_4870_ = v_a_4857_;
v___y_4871_ = v_a_4858_;
goto v___jp_4860_;
}
else
{
lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
lean_inc_ref(v_a_4846_);
v___x_4980_ = l_Lean_MessageData_ofExpr(v_a_4846_);
v___x_4981_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4980_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
lean_inc_ref(v_b_4847_);
v___x_4983_ = l_Lean_MessageData_ofExpr(v_b_4847_);
v___x_4984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4982_);
lean_ctor_set(v___x_4984_, 1, v___x_4983_);
v___x_4985_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(v___x_4976_, v___x_4984_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_dec_ref(v___x_4985_);
v___y_4861_ = v_val_4964_;
v___y_4862_ = v_a_4849_;
v___y_4863_ = v_a_4850_;
v___y_4864_ = v_a_4851_;
v___y_4865_ = v_a_4852_;
v___y_4866_ = v_a_4853_;
v___y_4867_ = v_a_4854_;
v___y_4868_ = v_a_4855_;
v___y_4869_ = v_a_4856_;
v___y_4870_ = v_a_4857_;
v___y_4871_ = v_a_4858_;
goto v___jp_4860_;
}
else
{
lean_dec(v_val_4964_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
return v___x_4985_;
}
}
}
}
else
{
lean_object* v___x_4986_; lean_object* v___x_4988_; 
lean_dec(v_a_4966_);
lean_dec(v_val_4964_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v___x_4986_ = lean_box(0);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_4986_);
v___x_4988_ = v___x_4968_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
v___x_4988_ = v_reuseFailAlloc_4989_;
goto v_reusejp_4987_;
}
v_reusejp_4987_:
{
return v___x_4988_;
}
}
}
}
else
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
lean_dec(v_val_4964_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4991_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4965_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4965_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
return v___x_4996_;
}
}
}
}
else
{
lean_object* v___x_4999_; lean_object* v___x_5001_; 
lean_dec(v_a_4960_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v___x_4999_ = lean_box(0);
if (v_isShared_4963_ == 0)
{
lean_ctor_set(v___x_4962_, 0, v___x_4999_);
v___x_5001_ = v___x_4962_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v___x_4999_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
lean_dec(v_a_4856_);
lean_dec_ref(v_a_4855_);
lean_dec(v_a_4854_);
lean_dec_ref(v_a_4853_);
lean_dec(v_a_4852_);
lean_dec_ref(v_a_4851_);
lean_dec(v_a_4850_);
lean_dec(v_a_4849_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_5004_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4959_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4959_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
v___jp_4860_:
{
lean_object* v___x_4872_; 
lean_inc_ref(v_a_4846_);
v___x_4872_ = l_Lean_Meta_Grind_Order_getNodeId(v_a_4846_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref(v___x_4872_);
lean_inc_ref(v_b_4847_);
v___x_4874_ = l_Lean_Meta_Grind_Order_getNodeId(v_b_4847_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4874_) == 0)
{
lean_object* v_a_4875_; lean_object* v___x_4876_; 
v_a_4875_ = lean_ctor_get(v___x_4874_, 0);
lean_inc(v_a_4875_);
lean_dec_ref(v___x_4874_);
v___x_4876_ = l_Lean_Meta_Grind_Order_isRing(v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; uint8_t v___x_4878_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v___x_4878_ = lean_unbox(v_a_4877_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4879_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4880_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4879_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
lean_inc(v_a_4881_);
lean_dec_ref(v___x_4880_);
v___x_4882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4883_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4882_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; uint8_t v___x_4888_; lean_object* v___x_4889_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref(v___x_4883_);
lean_inc_ref(v_h_4848_);
lean_inc_ref(v_b_4847_);
lean_inc_ref(v_a_4846_);
v___x_4885_ = l_Lean_mkApp3(v_a_4881_, v_a_4846_, v_b_4847_, v_h_4848_);
v___x_4886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4887_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
v___x_4888_ = lean_unbox(v_a_4877_);
lean_dec(v_a_4877_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*1, v___x_4888_);
lean_inc(v___y_4871_);
lean_inc_ref(v___y_4870_);
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
lean_inc_ref(v___y_4866_);
lean_inc(v___y_4865_);
lean_inc_ref(v___y_4864_);
lean_inc(v___y_4863_);
lean_inc(v___y_4862_);
lean_inc(v___y_4861_);
lean_inc_ref(v___x_4887_);
lean_inc(v_a_4875_);
lean_inc(v_a_4873_);
v___x_4889_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4873_, v_a_4875_, v___x_4887_, v___x_4885_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
lean_dec_ref(v___x_4889_);
v___x_4890_ = l_Lean_mkApp3(v_a_4884_, v_a_4846_, v_b_4847_, v_h_4848_);
v___x_4891_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4875_, v_a_4873_, v___x_4887_, v___x_4890_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
return v___x_4891_;
}
else
{
lean_dec_ref(v___x_4887_);
lean_dec(v_a_4884_);
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
return v___x_4889_;
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_a_4881_);
lean_dec(v_a_4877_);
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4892_ = lean_ctor_get(v___x_4883_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4883_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4883_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4907_; 
lean_dec(v_a_4877_);
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4900_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4880_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4880_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4905_; 
if (v_isShared_4903_ == 0)
{
v___x_4905_ = v___x_4902_;
goto v_reusejp_4904_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4900_);
v___x_4905_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4904_;
}
v_reusejp_4904_:
{
return v___x_4905_;
}
}
}
}
else
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_dec(v_a_4877_);
v___x_4908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4909_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4908_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v_a_4910_ = lean_ctor_get(v___x_4909_, 0);
lean_inc(v_a_4910_);
lean_dec_ref(v___x_4909_);
v___x_4911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4912_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4911_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref(v___x_4912_);
lean_inc_ref(v_h_4848_);
lean_inc_ref(v_b_4847_);
lean_inc_ref(v_a_4846_);
v___x_4914_ = l_Lean_mkApp3(v_a_4910_, v_a_4846_, v_b_4847_, v_h_4848_);
v___x_4915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v___y_4871_);
lean_inc_ref(v___y_4870_);
lean_inc(v___y_4869_);
lean_inc_ref(v___y_4868_);
lean_inc(v___y_4867_);
lean_inc_ref(v___y_4866_);
lean_inc(v___y_4865_);
lean_inc_ref(v___y_4864_);
lean_inc(v___y_4863_);
lean_inc(v___y_4862_);
lean_inc(v___y_4861_);
lean_inc(v_a_4875_);
lean_inc(v_a_4873_);
v___x_4916_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4873_, v_a_4875_, v___x_4915_, v___x_4914_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_dec_ref(v___x_4916_);
v___x_4917_ = l_Lean_mkApp3(v_a_4913_, v_a_4846_, v_b_4847_, v_h_4848_);
v___x_4918_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4875_, v_a_4873_, v___x_4915_, v___x_4917_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
return v___x_4918_;
}
else
{
lean_dec(v_a_4913_);
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
return v___x_4916_;
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec(v_a_4910_);
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4919_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4912_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4912_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
else
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4927_ = lean_ctor_get(v___x_4909_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4909_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4909_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4909_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
}
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
lean_dec(v_a_4875_);
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4935_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4876_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4876_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
else
{
lean_object* v_a_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4950_; 
lean_dec(v_a_4873_);
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4943_ = lean_ctor_get(v___x_4874_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4874_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4874_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4948_; 
if (v_isShared_4946_ == 0)
{
v___x_4948_ = v___x_4945_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
else
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4958_; 
lean_dec(v___y_4871_);
lean_dec_ref(v___y_4870_);
lean_dec(v___y_4869_);
lean_dec_ref(v___y_4868_);
lean_dec(v___y_4867_);
lean_dec_ref(v___y_4866_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v_h_4848_);
lean_dec_ref(v_b_4847_);
lean_dec_ref(v_a_4846_);
v_a_4951_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4953_ = v___x_4872_;
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4872_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4958_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
lean_object* v___x_4956_; 
if (v_isShared_4954_ == 0)
{
v___x_4956_ = v___x_4953_;
goto v_reusejp_4955_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4957_, 0, v_a_4951_);
v___x_4956_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4955_;
}
v_reusejp_4955_:
{
return v___x_4956_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_5012_, lean_object* v_b_5013_, lean_object* v_h_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_){
_start:
{
lean_object* v_res_5026_; 
v_res_5026_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_5012_, v_b_5013_, v_h_5014_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_, v_a_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_, v_a_5024_);
return v_res_5026_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
v___x_5033_ = lean_box(0);
v___x_5034_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_5035_ = l_Lean_mkConst(v___x_5034_, v___x_5033_);
return v___x_5035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_5036_, lean_object* v_b_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_){
_start:
{
uint8_t v___x_5049_; 
v___x_5049_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_5036_, v_b_5037_);
if (v___x_5049_ == 0)
{
lean_object* v___x_5050_; 
lean_inc(v_a_5047_);
lean_inc_ref(v_a_5046_);
lean_inc(v_a_5045_);
lean_inc_ref(v_a_5044_);
lean_inc(v_a_5043_);
lean_inc_ref(v_a_5042_);
lean_inc(v_a_5041_);
lean_inc_ref(v_a_5040_);
lean_inc(v_a_5039_);
lean_inc(v_a_5038_);
lean_inc_ref(v_b_5037_);
lean_inc_ref(v_a_5036_);
v___x_5050_ = lean_grind_mk_eq_proof(v_a_5036_, v_b_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
if (lean_obj_tag(v___x_5050_) == 0)
{
lean_object* v_a_5051_; lean_object* v___x_5052_; 
v_a_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc(v_a_5051_);
lean_dec_ref(v___x_5050_);
v___x_5052_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_5036_, v_a_5038_, v_a_5046_);
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref(v___x_5052_);
if (lean_obj_tag(v_a_5053_) == 1)
{
lean_object* v_val_5054_; lean_object* v_fst_5055_; lean_object* v_snd_5056_; lean_object* v___x_5057_; 
v_val_5054_ = lean_ctor_get(v_a_5053_, 0);
lean_inc(v_val_5054_);
lean_dec_ref(v_a_5053_);
v_fst_5055_ = lean_ctor_get(v_val_5054_, 0);
lean_inc(v_fst_5055_);
v_snd_5056_ = lean_ctor_get(v_val_5054_, 1);
lean_inc(v_snd_5056_);
lean_dec(v_val_5054_);
v___x_5057_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_5037_, v_a_5038_, v_a_5046_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5072_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5060_ = v___x_5057_;
v_isShared_5061_ = v_isSharedCheck_5072_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_5057_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5072_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
if (lean_obj_tag(v_a_5058_) == 1)
{
lean_object* v_val_5062_; lean_object* v_fst_5063_; lean_object* v_snd_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; 
lean_del_object(v___x_5060_);
v_val_5062_ = lean_ctor_get(v_a_5058_, 0);
lean_inc(v_val_5062_);
lean_dec_ref(v_a_5058_);
v_fst_5063_ = lean_ctor_get(v_val_5062_, 0);
lean_inc(v_fst_5063_);
v_snd_5064_ = lean_ctor_get(v_val_5062_, 1);
lean_inc(v_snd_5064_);
lean_dec(v_val_5062_);
v___x_5065_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__2, &l_Lean_Meta_Grind_Order_processNewEq___closed__2_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2);
lean_inc(v_fst_5063_);
lean_inc(v_fst_5055_);
v___x_5066_ = l_Lean_mkApp7(v___x_5065_, v_a_5036_, v_b_5037_, v_fst_5055_, v_fst_5063_, v_snd_5056_, v_snd_5064_, v_a_5051_);
v___x_5067_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_fst_5055_, v_fst_5063_, v___x_5066_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
return v___x_5067_;
}
else
{
lean_object* v___x_5068_; lean_object* v___x_5070_; 
lean_dec(v_a_5058_);
lean_dec(v_snd_5056_);
lean_dec(v_fst_5055_);
lean_dec(v_a_5051_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_b_5037_);
lean_dec_ref(v_a_5036_);
v___x_5068_ = lean_box(0);
if (v_isShared_5061_ == 0)
{
lean_ctor_set(v___x_5060_, 0, v___x_5068_);
v___x_5070_ = v___x_5060_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v___x_5068_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
else
{
lean_object* v_a_5073_; lean_object* v___x_5075_; uint8_t v_isShared_5076_; uint8_t v_isSharedCheck_5080_; 
lean_dec(v_snd_5056_);
lean_dec(v_fst_5055_);
lean_dec(v_a_5051_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_b_5037_);
lean_dec_ref(v_a_5036_);
v_a_5073_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5080_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5080_ == 0)
{
v___x_5075_ = v___x_5057_;
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
else
{
lean_inc(v_a_5073_);
lean_dec(v___x_5057_);
v___x_5075_ = lean_box(0);
v_isShared_5076_ = v_isSharedCheck_5080_;
goto v_resetjp_5074_;
}
v_resetjp_5074_:
{
lean_object* v___x_5078_; 
if (v_isShared_5076_ == 0)
{
v___x_5078_ = v___x_5075_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5079_; 
v_reuseFailAlloc_5079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5079_, 0, v_a_5073_);
v___x_5078_ = v_reuseFailAlloc_5079_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
return v___x_5078_;
}
}
}
}
else
{
lean_object* v___x_5081_; 
lean_dec(v_a_5053_);
v___x_5081_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_5036_, v_b_5037_, v_a_5051_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_);
return v___x_5081_;
}
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_dec(v_a_5051_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_b_5037_);
lean_dec_ref(v_a_5036_);
v_a_5082_ = lean_ctor_get(v___x_5052_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5052_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5052_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5052_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
else
{
lean_object* v_a_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5097_; 
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_b_5037_);
lean_dec_ref(v_a_5036_);
v_a_5090_ = lean_ctor_get(v___x_5050_, 0);
v_isSharedCheck_5097_ = !lean_is_exclusive(v___x_5050_);
if (v_isSharedCheck_5097_ == 0)
{
v___x_5092_ = v___x_5050_;
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_a_5090_);
lean_dec(v___x_5050_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5097_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5095_; 
if (v_isShared_5093_ == 0)
{
v___x_5095_ = v___x_5092_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5096_; 
v_reuseFailAlloc_5096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
v___x_5095_ = v_reuseFailAlloc_5096_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
return v___x_5095_;
}
}
}
}
else
{
lean_object* v___x_5098_; lean_object* v___x_5099_; 
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
lean_dec(v_a_5045_);
lean_dec_ref(v_a_5044_);
lean_dec(v_a_5043_);
lean_dec_ref(v_a_5042_);
lean_dec(v_a_5041_);
lean_dec_ref(v_a_5040_);
lean_dec(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_b_5037_);
lean_dec_ref(v_a_5036_);
v___x_5098_ = lean_box(0);
v___x_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5099_, 0, v___x_5098_);
return v___x_5099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5100_, lean_object* v_b_5101_, lean_object* v_a_5102_, lean_object* v_a_5103_, lean_object* v_a_5104_, lean_object* v_a_5105_, lean_object* v_a_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5100_, v_b_5101_, v_a_5102_, v_a_5103_, v_a_5104_, v_a_5105_, v_a_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_, v_a_5111_);
return v_res_5113_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Order(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Init_Grind_Order(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Order_OrderM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Order_Assert(builtin);
}
#ifdef __cplusplus
}
#endif
