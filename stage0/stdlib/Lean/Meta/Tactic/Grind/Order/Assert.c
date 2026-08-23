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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object*, lean_object*);
lean_object* l_Ordering_ctorIdx(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_Lean_AssocList_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "-ε"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5_value;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_value;
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
static lean_once_cell_t l_Lean_Meta_Grind_Order_addEdge___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_addEdge___closed__2;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5;
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
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Order_processNewEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Order_processNewEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "of_natCast_eq"};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 229, 71, 248, 88, 192, 235, 207)}};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Order_processNewEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_nat_eq"};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(190, 179, 250, 96, 74, 22, 134, 180)}};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Order_processNewEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__6;
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
lean_dec_ref_known(v___x_19_, 1);
v___x_21_ = l_Lean_Meta_Grind_Order_mkTrans(v_a_20_, v_p_3_, v_v_2_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_21_, 1);
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
lean_dec_ref_known(v___x_71_, 1);
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
lean_dec_ref_known(v___x_114_, 1);
v___x_116_ = l_Lean_Meta_Grind_Order_getExpr(v_u_97_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_Meta_Grind_Order_getExpr(v_v_98_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_a_117_, v_a_119_, v_kuv_99_, v_huv_100_, v_kvu_101_, v_a_115_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = l_Lean_Meta_Grind_closeGoal(v_a_121_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
return v___x_122_;
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
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
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec(v_a_161_);
lean_dec(v_a_160_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object* v_u_208_, lean_object* v_k_209_, lean_object* v_x_210_, size_t v_x_211_, size_t v_x_212_){
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
v___x_230_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_208_, v_k_209_, v_v_227_, v_i_224_, v_shift_226_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object* v_u_254_, lean_object* v_k_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
size_t v_x_294__boxed_259_; size_t v_x_295__boxed_260_; lean_object* v_res_261_; 
v_x_294__boxed_259_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_295__boxed_260_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_261_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_254_, v_k_255_, v_x_256_, v_x_294__boxed_259_, v_x_295__boxed_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object* v_u_262_, lean_object* v_k_263_, lean_object* v_t_264_, lean_object* v_i_265_){
_start:
{
lean_object* v_root_266_; lean_object* v_tail_267_; lean_object* v_size_268_; size_t v_shift_269_; lean_object* v_tailOff_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_294_; 
v_root_266_ = lean_ctor_get(v_t_264_, 0);
v_tail_267_ = lean_ctor_get(v_t_264_, 1);
v_size_268_ = lean_ctor_get(v_t_264_, 2);
v_shift_269_ = lean_ctor_get_usize(v_t_264_, 4);
v_tailOff_270_ = lean_ctor_get(v_t_264_, 3);
v_isSharedCheck_294_ = !lean_is_exclusive(v_t_264_);
if (v_isSharedCheck_294_ == 0)
{
v___x_272_ = v_t_264_;
v_isShared_273_ = v_isSharedCheck_294_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_tailOff_270_);
lean_inc(v_size_268_);
lean_inc(v_tail_267_);
lean_inc(v_root_266_);
lean_dec(v_t_264_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_294_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_le(v_tailOff_270_, v_i_265_);
if (v___x_274_ == 0)
{
size_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_usize_of_nat(v_i_265_);
v___x_276_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_262_, v_k_263_, v_root_266_, v___x_275_, v_shift_269_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_tail_267_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_size_268_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_tailOff_270_);
lean_ctor_set_usize(v_reuseFailAlloc_279_, 4, v_shift_269_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_nat_sub(v_i_265_, v_tailOff_270_);
v___x_281_ = lean_array_get_size(v_tail_267_);
v___x_282_ = lean_nat_dec_lt(v___x_280_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v___x_280_);
lean_dec_ref(v_k_263_);
lean_dec(v_u_262_);
if (v_isShared_273_ == 0)
{
v___x_284_ = v___x_272_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_root_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_tail_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_size_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_tailOff_270_);
lean_ctor_set_usize(v_reuseFailAlloc_285_, 4, v_shift_269_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
else
{
lean_object* v_v_286_; lean_object* v___x_287_; lean_object* v_xs_x27_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v_v_286_ = lean_array_fget(v_tail_267_, v___x_280_);
v___x_287_ = lean_box(0);
v_xs_x27_288_ = lean_array_fset(v_tail_267_, v___x_280_, v___x_287_);
v___x_289_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_286_, v_u_262_, v_k_263_);
v___x_290_ = lean_array_fset(v_xs_x27_288_, v___x_280_, v___x_289_);
lean_dec(v___x_280_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_290_);
v___x_292_ = v___x_272_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_root_266_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_size_268_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_tailOff_270_);
lean_ctor_set_usize(v_reuseFailAlloc_293_, 4, v_shift_269_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object* v_u_295_, lean_object* v_k_296_, lean_object* v_t_297_, lean_object* v_i_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_295_, v_k_296_, v_t_297_, v_i_298_);
lean_dec(v_i_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object* v_u_300_, lean_object* v_k_301_, lean_object* v_v_302_, lean_object* v_s_303_){
_start:
{
lean_object* v_id_304_; lean_object* v_type_305_; lean_object* v_u_306_; lean_object* v_isPreorderInst_307_; lean_object* v_leInst_308_; lean_object* v_ltInst_x3f_309_; lean_object* v_isPartialInst_x3f_310_; lean_object* v_isLinearPreInst_x3f_311_; lean_object* v_lawfulOrderLTInst_x3f_312_; lean_object* v_ringId_x3f_313_; uint8_t v_isCommRing_314_; lean_object* v_ringInst_x3f_315_; lean_object* v_orderedRingInst_x3f_316_; lean_object* v_leFn_317_; lean_object* v_ltFn_x3f_318_; lean_object* v_nodes_319_; lean_object* v_nodeMap_320_; lean_object* v_cnstrs_321_; lean_object* v_cnstrsOf_322_; lean_object* v_sources_323_; lean_object* v_targets_324_; lean_object* v_proofs_325_; lean_object* v_propagate_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_335_; 
v_id_304_ = lean_ctor_get(v_s_303_, 0);
v_type_305_ = lean_ctor_get(v_s_303_, 1);
v_u_306_ = lean_ctor_get(v_s_303_, 2);
v_isPreorderInst_307_ = lean_ctor_get(v_s_303_, 3);
v_leInst_308_ = lean_ctor_get(v_s_303_, 4);
v_ltInst_x3f_309_ = lean_ctor_get(v_s_303_, 5);
v_isPartialInst_x3f_310_ = lean_ctor_get(v_s_303_, 6);
v_isLinearPreInst_x3f_311_ = lean_ctor_get(v_s_303_, 7);
v_lawfulOrderLTInst_x3f_312_ = lean_ctor_get(v_s_303_, 8);
v_ringId_x3f_313_ = lean_ctor_get(v_s_303_, 9);
v_isCommRing_314_ = lean_ctor_get_uint8(v_s_303_, sizeof(void*)*22);
v_ringInst_x3f_315_ = lean_ctor_get(v_s_303_, 10);
v_orderedRingInst_x3f_316_ = lean_ctor_get(v_s_303_, 11);
v_leFn_317_ = lean_ctor_get(v_s_303_, 12);
v_ltFn_x3f_318_ = lean_ctor_get(v_s_303_, 13);
v_nodes_319_ = lean_ctor_get(v_s_303_, 14);
v_nodeMap_320_ = lean_ctor_get(v_s_303_, 15);
v_cnstrs_321_ = lean_ctor_get(v_s_303_, 16);
v_cnstrsOf_322_ = lean_ctor_get(v_s_303_, 17);
v_sources_323_ = lean_ctor_get(v_s_303_, 18);
v_targets_324_ = lean_ctor_get(v_s_303_, 19);
v_proofs_325_ = lean_ctor_get(v_s_303_, 20);
v_propagate_326_ = lean_ctor_get(v_s_303_, 21);
v_isSharedCheck_335_ = !lean_is_exclusive(v_s_303_);
if (v_isSharedCheck_335_ == 0)
{
v___x_328_ = v_s_303_;
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_propagate_326_);
lean_inc(v_proofs_325_);
lean_inc(v_targets_324_);
lean_inc(v_sources_323_);
lean_inc(v_cnstrsOf_322_);
lean_inc(v_cnstrs_321_);
lean_inc(v_nodeMap_320_);
lean_inc(v_nodes_319_);
lean_inc(v_ltFn_x3f_318_);
lean_inc(v_leFn_317_);
lean_inc(v_orderedRingInst_x3f_316_);
lean_inc(v_ringInst_x3f_315_);
lean_inc(v_ringId_x3f_313_);
lean_inc(v_lawfulOrderLTInst_x3f_312_);
lean_inc(v_isLinearPreInst_x3f_311_);
lean_inc(v_isPartialInst_x3f_310_);
lean_inc(v_ltInst_x3f_309_);
lean_inc(v_leInst_308_);
lean_inc(v_isPreorderInst_307_);
lean_inc(v_u_306_);
lean_inc(v_type_305_);
lean_inc(v_id_304_);
lean_dec(v_s_303_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_335_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_inc_ref(v_k_301_);
lean_inc(v_u_300_);
v___x_330_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_300_, v_k_301_, v_sources_323_, v_v_302_);
v___x_331_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_v_302_, v_k_301_, v_targets_324_, v_u_300_);
lean_dec(v_u_300_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 19, v___x_331_);
lean_ctor_set(v___x_328_, 18, v___x_330_);
v___x_333_ = v___x_328_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_id_304_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_type_305_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_u_306_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_isPreorderInst_307_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_leInst_308_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v_ltInst_x3f_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_isPartialInst_x3f_310_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_isLinearPreInst_x3f_311_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v_lawfulOrderLTInst_x3f_312_);
lean_ctor_set(v_reuseFailAlloc_334_, 9, v_ringId_x3f_313_);
lean_ctor_set(v_reuseFailAlloc_334_, 10, v_ringInst_x3f_315_);
lean_ctor_set(v_reuseFailAlloc_334_, 11, v_orderedRingInst_x3f_316_);
lean_ctor_set(v_reuseFailAlloc_334_, 12, v_leFn_317_);
lean_ctor_set(v_reuseFailAlloc_334_, 13, v_ltFn_x3f_318_);
lean_ctor_set(v_reuseFailAlloc_334_, 14, v_nodes_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 15, v_nodeMap_320_);
lean_ctor_set(v_reuseFailAlloc_334_, 16, v_cnstrs_321_);
lean_ctor_set(v_reuseFailAlloc_334_, 17, v_cnstrsOf_322_);
lean_ctor_set(v_reuseFailAlloc_334_, 18, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_334_, 19, v___x_331_);
lean_ctor_set(v_reuseFailAlloc_334_, 20, v_proofs_325_);
lean_ctor_set(v_reuseFailAlloc_334_, 21, v_propagate_326_);
lean_ctor_set_uint8(v_reuseFailAlloc_334_, sizeof(void*)*22, v_isCommRing_314_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object* v_u_336_, lean_object* v_v_337_, lean_object* v_k_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___f_342_; lean_object* v___x_343_; 
v___f_342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0), 4, 3);
lean_closure_set(v___f_342_, 0, v_u_336_);
lean_closure_set(v___f_342_, 1, v_k_338_);
lean_closure_set(v___f_342_, 2, v_v_337_);
v___x_343_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_342_, v_a_339_, v_a_340_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object* v_u_344_, lean_object* v_v_345_, lean_object* v_k_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_344_, v_v_345_, v_k_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec(v_a_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object* v_u_351_, lean_object* v_v_352_, lean_object* v_k_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_351_, v_v_352_, v_k_353_, v_a_354_, v_a_355_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object* v_u_367_, lean_object* v_v_368_, lean_object* v_k_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(v_u_367_, v_v_368_, v_k_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec(v_a_371_);
lean_dec(v_a_370_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object* v_00_u03b2_383_, lean_object* v_m_384_, lean_object* v_k_385_, lean_object* v_v_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_m_384_, v_k_385_, v_v_386_);
return v___x_387_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object* v_00_u03b2_388_, lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_389_, v_x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_392_, lean_object* v_a_393_, lean_object* v_x_394_){
_start:
{
uint8_t v_res_395_; lean_object* v_r_396_; 
v_res_395_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(v_00_u03b2_392_, v_a_393_, v_x_394_);
lean_dec(v_x_394_);
lean_dec(v_a_393_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object* v_00_u03b2_397_, lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_398_, v_b_399_, v_x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object* v_v_402_, lean_object* v_p_403_, lean_object* v_x_404_, size_t v_x_405_, size_t v_x_406_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v_cs_407_; size_t v_j_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_cs_407_ = lean_ctor_get(v_x_404_, 0);
v_j_408_ = lean_usize_shift_right(v_x_405_, v_x_406_);
v___x_409_ = lean_usize_to_nat(v_j_408_);
v___x_410_ = lean_array_get_size(v_cs_407_);
v___x_411_ = lean_nat_dec_lt(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec(v___x_409_);
lean_dec_ref(v_p_403_);
lean_dec(v_v_402_);
return v_x_404_;
}
else
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_429_; 
lean_inc_ref(v_cs_407_);
v_isSharedCheck_429_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_x_404_, 0);
lean_dec(v_unused_430_);
v___x_413_ = v_x_404_;
v_isShared_414_ = v_isSharedCheck_429_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_x_404_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_429_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
size_t v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v_i_418_; size_t v___x_419_; size_t v_shift_420_; lean_object* v_v_421_; lean_object* v___x_422_; lean_object* v_xs_x27_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_shift_left(v___x_415_, v_x_406_);
v___x_417_ = lean_usize_sub(v___x_416_, v___x_415_);
v_i_418_ = lean_usize_land(v_x_405_, v___x_417_);
v___x_419_ = ((size_t)5ULL);
v_shift_420_ = lean_usize_sub(v_x_406_, v___x_419_);
v_v_421_ = lean_array_fget(v_cs_407_, v___x_409_);
v___x_422_ = lean_box(0);
v_xs_x27_423_ = lean_array_fset(v_cs_407_, v___x_409_, v___x_422_);
v___x_424_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_402_, v_p_403_, v_v_421_, v_i_418_, v_shift_420_);
v___x_425_ = lean_array_fset(v_xs_x27_423_, v___x_409_, v___x_424_);
lean_dec(v___x_409_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_425_);
v___x_427_ = v___x_413_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_vs_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_vs_431_ = lean_ctor_get(v_x_404_, 0);
v___x_432_ = lean_usize_to_nat(v_x_405_);
v___x_433_ = lean_array_get_size(v_vs_431_);
v___x_434_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_dec(v___x_432_);
lean_dec_ref(v_p_403_);
lean_dec(v_v_402_);
return v_x_404_;
}
else
{
lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_446_; 
lean_inc_ref(v_vs_431_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_x_404_, 0);
lean_dec(v_unused_447_);
v___x_436_ = v_x_404_;
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
else
{
lean_dec(v_x_404_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_v_438_; lean_object* v___x_439_; lean_object* v_xs_x27_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_v_438_ = lean_array_fget(v_vs_431_, v___x_432_);
v___x_439_ = lean_box(0);
v_xs_x27_440_ = lean_array_fset(v_vs_431_, v___x_432_, v___x_439_);
v___x_441_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_438_, v_v_402_, v_p_403_);
v___x_442_ = lean_array_fset(v_xs_x27_440_, v___x_432_, v___x_441_);
lean_dec(v___x_432_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_442_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object* v_v_448_, lean_object* v_p_449_, lean_object* v_x_450_, lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
size_t v_x_152__boxed_453_; size_t v_x_153__boxed_454_; lean_object* v_res_455_; 
v_x_152__boxed_453_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_x_153__boxed_454_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_res_455_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_448_, v_p_449_, v_x_450_, v_x_152__boxed_453_, v_x_153__boxed_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object* v_v_456_, lean_object* v_p_457_, lean_object* v_t_458_, lean_object* v_i_459_){
_start:
{
lean_object* v_root_460_; lean_object* v_tail_461_; lean_object* v_size_462_; size_t v_shift_463_; lean_object* v_tailOff_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_488_; 
v_root_460_ = lean_ctor_get(v_t_458_, 0);
v_tail_461_ = lean_ctor_get(v_t_458_, 1);
v_size_462_ = lean_ctor_get(v_t_458_, 2);
v_shift_463_ = lean_ctor_get_usize(v_t_458_, 4);
v_tailOff_464_ = lean_ctor_get(v_t_458_, 3);
v_isSharedCheck_488_ = !lean_is_exclusive(v_t_458_);
if (v_isSharedCheck_488_ == 0)
{
v___x_466_ = v_t_458_;
v_isShared_467_ = v_isSharedCheck_488_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_tailOff_464_);
lean_inc(v_size_462_);
lean_inc(v_tail_461_);
lean_inc(v_root_460_);
lean_dec(v_t_458_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_488_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_le(v_tailOff_464_, v_i_459_);
if (v___x_468_ == 0)
{
size_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_usize_of_nat(v_i_459_);
v___x_470_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_456_, v_p_457_, v_root_460_, v___x_469_, v_shift_463_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_470_);
v___x_472_ = v___x_466_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_tail_461_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_size_462_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_tailOff_464_);
lean_ctor_set_usize(v_reuseFailAlloc_473_, 4, v_shift_463_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_474_ = lean_nat_sub(v_i_459_, v_tailOff_464_);
v___x_475_ = lean_array_get_size(v_tail_461_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v___x_474_);
lean_dec_ref(v_p_457_);
lean_dec(v_v_456_);
if (v_isShared_467_ == 0)
{
v___x_478_ = v___x_466_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_root_460_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_tail_461_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_size_462_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_tailOff_464_);
lean_ctor_set_usize(v_reuseFailAlloc_479_, 4, v_shift_463_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v_v_480_; lean_object* v___x_481_; lean_object* v_xs_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v_v_480_ = lean_array_fget(v_tail_461_, v___x_474_);
v___x_481_ = lean_box(0);
v_xs_x27_482_ = lean_array_fset(v_tail_461_, v___x_474_, v___x_481_);
v___x_483_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_480_, v_v_456_, v_p_457_);
v___x_484_ = lean_array_fset(v_xs_x27_482_, v___x_474_, v___x_483_);
lean_dec(v___x_474_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 1, v___x_484_);
v___x_486_ = v___x_466_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_root_460_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v_size_462_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_tailOff_464_);
lean_ctor_set_usize(v_reuseFailAlloc_487_, 4, v_shift_463_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object* v_v_489_, lean_object* v_p_490_, lean_object* v_t_491_, lean_object* v_i_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_489_, v_p_490_, v_t_491_, v_i_492_);
lean_dec(v_i_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object* v_v_494_, lean_object* v_p_495_, lean_object* v_u_496_, lean_object* v_s_497_){
_start:
{
lean_object* v_id_498_; lean_object* v_type_499_; lean_object* v_u_500_; lean_object* v_isPreorderInst_501_; lean_object* v_leInst_502_; lean_object* v_ltInst_x3f_503_; lean_object* v_isPartialInst_x3f_504_; lean_object* v_isLinearPreInst_x3f_505_; lean_object* v_lawfulOrderLTInst_x3f_506_; lean_object* v_ringId_x3f_507_; uint8_t v_isCommRing_508_; lean_object* v_ringInst_x3f_509_; lean_object* v_orderedRingInst_x3f_510_; lean_object* v_leFn_511_; lean_object* v_ltFn_x3f_512_; lean_object* v_nodes_513_; lean_object* v_nodeMap_514_; lean_object* v_cnstrs_515_; lean_object* v_cnstrsOf_516_; lean_object* v_sources_517_; lean_object* v_targets_518_; lean_object* v_proofs_519_; lean_object* v_propagate_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_528_; 
v_id_498_ = lean_ctor_get(v_s_497_, 0);
v_type_499_ = lean_ctor_get(v_s_497_, 1);
v_u_500_ = lean_ctor_get(v_s_497_, 2);
v_isPreorderInst_501_ = lean_ctor_get(v_s_497_, 3);
v_leInst_502_ = lean_ctor_get(v_s_497_, 4);
v_ltInst_x3f_503_ = lean_ctor_get(v_s_497_, 5);
v_isPartialInst_x3f_504_ = lean_ctor_get(v_s_497_, 6);
v_isLinearPreInst_x3f_505_ = lean_ctor_get(v_s_497_, 7);
v_lawfulOrderLTInst_x3f_506_ = lean_ctor_get(v_s_497_, 8);
v_ringId_x3f_507_ = lean_ctor_get(v_s_497_, 9);
v_isCommRing_508_ = lean_ctor_get_uint8(v_s_497_, sizeof(void*)*22);
v_ringInst_x3f_509_ = lean_ctor_get(v_s_497_, 10);
v_orderedRingInst_x3f_510_ = lean_ctor_get(v_s_497_, 11);
v_leFn_511_ = lean_ctor_get(v_s_497_, 12);
v_ltFn_x3f_512_ = lean_ctor_get(v_s_497_, 13);
v_nodes_513_ = lean_ctor_get(v_s_497_, 14);
v_nodeMap_514_ = lean_ctor_get(v_s_497_, 15);
v_cnstrs_515_ = lean_ctor_get(v_s_497_, 16);
v_cnstrsOf_516_ = lean_ctor_get(v_s_497_, 17);
v_sources_517_ = lean_ctor_get(v_s_497_, 18);
v_targets_518_ = lean_ctor_get(v_s_497_, 19);
v_proofs_519_ = lean_ctor_get(v_s_497_, 20);
v_propagate_520_ = lean_ctor_get(v_s_497_, 21);
v_isSharedCheck_528_ = !lean_is_exclusive(v_s_497_);
if (v_isSharedCheck_528_ == 0)
{
v___x_522_ = v_s_497_;
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_propagate_520_);
lean_inc(v_proofs_519_);
lean_inc(v_targets_518_);
lean_inc(v_sources_517_);
lean_inc(v_cnstrsOf_516_);
lean_inc(v_cnstrs_515_);
lean_inc(v_nodeMap_514_);
lean_inc(v_nodes_513_);
lean_inc(v_ltFn_x3f_512_);
lean_inc(v_leFn_511_);
lean_inc(v_orderedRingInst_x3f_510_);
lean_inc(v_ringInst_x3f_509_);
lean_inc(v_ringId_x3f_507_);
lean_inc(v_lawfulOrderLTInst_x3f_506_);
lean_inc(v_isLinearPreInst_x3f_505_);
lean_inc(v_isPartialInst_x3f_504_);
lean_inc(v_ltInst_x3f_503_);
lean_inc(v_leInst_502_);
lean_inc(v_isPreorderInst_501_);
lean_inc(v_u_500_);
lean_inc(v_type_499_);
lean_inc(v_id_498_);
lean_dec(v_s_497_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_528_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_494_, v_p_495_, v_proofs_519_, v_u_496_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 20, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_id_498_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_type_499_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_u_500_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_isPreorderInst_501_);
lean_ctor_set(v_reuseFailAlloc_527_, 4, v_leInst_502_);
lean_ctor_set(v_reuseFailAlloc_527_, 5, v_ltInst_x3f_503_);
lean_ctor_set(v_reuseFailAlloc_527_, 6, v_isPartialInst_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_527_, 7, v_isLinearPreInst_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_527_, 8, v_lawfulOrderLTInst_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_527_, 9, v_ringId_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_527_, 10, v_ringInst_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_527_, 11, v_orderedRingInst_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_527_, 12, v_leFn_511_);
lean_ctor_set(v_reuseFailAlloc_527_, 13, v_ltFn_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_527_, 14, v_nodes_513_);
lean_ctor_set(v_reuseFailAlloc_527_, 15, v_nodeMap_514_);
lean_ctor_set(v_reuseFailAlloc_527_, 16, v_cnstrs_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 17, v_cnstrsOf_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 18, v_sources_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 19, v_targets_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 20, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_527_, 21, v_propagate_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*22, v_isCommRing_508_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object* v_v_529_, lean_object* v_p_530_, lean_object* v_u_531_, lean_object* v_s_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(v_v_529_, v_p_530_, v_u_531_, v_s_532_);
lean_dec(v_u_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object* v_u_534_, lean_object* v_v_535_, lean_object* v_p_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
v___f_540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_540_, 0, v_v_535_);
lean_closure_set(v___f_540_, 1, v_p_536_);
lean_closure_set(v___f_540_, 2, v_u_534_);
v___x_541_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_540_, v_a_537_, v_a_538_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object* v_u_542_, lean_object* v_v_543_, lean_object* v_p_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_542_, v_v_543_, v_p_544_, v_a_545_, v_a_546_);
lean_dec(v_a_546_);
lean_dec(v_a_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object* v_u_549_, lean_object* v_v_550_, lean_object* v_p_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_549_, v_v_550_, v_p_551_, v_a_552_, v_a_553_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object* v_u_565_, lean_object* v_v_566_, lean_object* v_p_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(v_u_565_, v_v_566_, v_p_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec(v_a_569_);
lean_dec(v_a_568_);
return v_res_580_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0(void){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_instMonadEIO(lean_box(0));
return v___x_581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0);
v___x_583_ = l_StateRefT_x27_instMonad___redArg(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object* v_u_588_, lean_object* v_f_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_toApplicative_603_; lean_object* v_toFunctor_604_; lean_object* v_toSeq_605_; lean_object* v_toSeqLeft_606_; lean_object* v_toSeqRight_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_toApplicative_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_673_; 
v___x_602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_603_ = lean_ctor_get(v___x_602_, 0);
v_toFunctor_604_ = lean_ctor_get(v_toApplicative_603_, 0);
v_toSeq_605_ = lean_ctor_get(v_toApplicative_603_, 2);
v_toSeqLeft_606_ = lean_ctor_get(v_toApplicative_603_, 3);
v_toSeqRight_607_ = lean_ctor_get(v_toApplicative_603_, 4);
v___f_608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_604_, 2);
v___f_610_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_610_, 0, v_toFunctor_604_);
v___f_611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_611_, 0, v_toFunctor_604_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___f_610_);
lean_ctor_set(v___x_612_, 1, v___f_611_);
lean_inc(v_toSeqRight_607_);
v___f_613_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_613_, 0, v_toSeqRight_607_);
lean_inc(v_toSeqLeft_606_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_614_, 0, v_toSeqLeft_606_);
lean_inc(v_toSeq_605_);
v___f_615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_615_, 0, v_toSeq_605_);
v___x_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_616_, 0, v___x_612_);
lean_ctor_set(v___x_616_, 1, v___f_608_);
lean_ctor_set(v___x_616_, 2, v___f_615_);
lean_ctor_set(v___x_616_, 3, v___f_614_);
lean_ctor_set(v___x_616_, 4, v___f_613_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___f_609_);
v___x_618_ = l_StateRefT_x27_instMonad___redArg(v___x_617_);
v_toApplicative_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_618_, 1);
lean_dec(v_unused_674_);
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_673_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_toApplicative_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_673_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v_toFunctor_623_; lean_object* v_toSeq_624_; lean_object* v_toSeqLeft_625_; lean_object* v_toSeqRight_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_671_; 
v_toFunctor_623_ = lean_ctor_get(v_toApplicative_619_, 0);
v_toSeq_624_ = lean_ctor_get(v_toApplicative_619_, 2);
v_toSeqLeft_625_ = lean_ctor_get(v_toApplicative_619_, 3);
v_toSeqRight_626_ = lean_ctor_get(v_toApplicative_619_, 4);
v_isSharedCheck_671_ = !lean_is_exclusive(v_toApplicative_619_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v_toApplicative_619_, 1);
lean_dec(v_unused_672_);
v___x_628_ = v_toApplicative_619_;
v_isShared_629_ = v_isSharedCheck_671_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_toSeqRight_626_);
lean_inc(v_toSeqLeft_625_);
lean_inc(v_toSeq_624_);
lean_inc(v_toFunctor_623_);
lean_dec(v_toApplicative_619_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_671_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___f_630_; lean_object* v___f_631_; lean_object* v___f_632_; lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_639_; 
v___f_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_623_);
v___f_632_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_632_, 0, v_toFunctor_623_);
v___f_633_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_633_, 0, v_toFunctor_623_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___f_632_);
lean_ctor_set(v___x_634_, 1, v___f_633_);
v___f_635_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_635_, 0, v_toSeqRight_626_);
v___f_636_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_636_, 0, v_toSeqLeft_625_);
v___f_637_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_637_, 0, v_toSeq_624_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 4, v___f_635_);
lean_ctor_set(v___x_628_, 3, v___f_636_);
lean_ctor_set(v___x_628_, 2, v___f_637_);
lean_ctor_set(v___x_628_, 1, v___f_630_);
lean_ctor_set(v___x_628_, 0, v___x_634_);
v___x_639_ = v___x_628_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___f_630_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___f_637_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v___f_636_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v___f_635_);
v___x_639_ = v_reuseFailAlloc_670_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_641_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 1, v___f_631_);
lean_ctor_set(v___x_621_, 0, v___x_639_);
v___x_641_ = v___x_621_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___f_631_);
v___x_641_ = v_reuseFailAlloc_669_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_642_ = l_StateRefT_x27_instMonad___redArg(v___x_641_);
v___x_643_ = l_ReaderT_instMonad___redArg(v___x_642_);
v___x_644_ = l_StateRefT_x27_instMonad___redArg(v___x_643_);
v___x_645_ = l_ReaderT_instMonad___redArg(v___x_644_);
v___x_646_ = l_ReaderT_instMonad___redArg(v___x_645_);
v___x_647_ = l_StateRefT_x27_instMonad___redArg(v___x_646_);
v___x_648_ = l_ReaderT_instMonad___redArg(v___x_647_);
v___x_649_ = l_Lean_Meta_Grind_Order_getStruct(v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v_sources_651_; lean_object* v_size_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v_sources_651_ = lean_ctor_get(v_a_650_, 18);
lean_inc_ref(v_sources_651_);
lean_dec(v_a_650_);
v_size_652_ = lean_ctor_get(v_sources_651_, 2);
v___x_653_ = lean_box(0);
v___x_654_ = lean_nat_dec_lt(v_u_588_, v_size_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_804__overap_656_; lean_object* v___x_657_; 
lean_dec_ref(v_sources_651_);
v___x_655_ = l_outOfBounds___redArg(v___x_653_);
v___x_804__overap_656_ = l_Lean_AssocList_forM___redArg(v___x_648_, v_f_589_, v___x_655_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
lean_inc(v_a_596_);
lean_inc_ref(v_a_595_);
lean_inc(v_a_594_);
lean_inc_ref(v_a_593_);
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_inc(v_a_590_);
v___x_657_ = lean_apply_12(v___x_804__overap_656_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_802__overap_659_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_PersistentArray_get_x21___redArg(v___x_653_, v_sources_651_, v_u_588_);
lean_dec_ref(v_sources_651_);
v___x_802__overap_659_ = l_Lean_AssocList_forM___redArg(v___x_648_, v_f_589_, v___x_658_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
lean_inc(v_a_598_);
lean_inc_ref(v_a_597_);
lean_inc(v_a_596_);
lean_inc_ref(v_a_595_);
lean_inc(v_a_594_);
lean_inc_ref(v_a_593_);
lean_inc(v_a_592_);
lean_inc(v_a_591_);
lean_inc(v_a_590_);
v___x_660_ = lean_apply_12(v___x_802__overap_659_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_660_;
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_f_589_);
v_a_661_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_649_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_649_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object* v_u_675_, lean_object* v_f_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(v_u_675_, v_f_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec(v_a_678_);
lean_dec(v_a_677_);
lean_dec(v_u_675_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object* v_u_690_, lean_object* v_f_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; lean_object* v_toApplicative_705_; lean_object* v_toFunctor_706_; lean_object* v_toSeq_707_; lean_object* v_toSeqLeft_708_; lean_object* v_toSeqRight_709_; lean_object* v___f_710_; lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___f_713_; lean_object* v___x_714_; lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_toApplicative_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_775_; 
v___x_704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_705_ = lean_ctor_get(v___x_704_, 0);
v_toFunctor_706_ = lean_ctor_get(v_toApplicative_705_, 0);
v_toSeq_707_ = lean_ctor_get(v_toApplicative_705_, 2);
v_toSeqLeft_708_ = lean_ctor_get(v_toApplicative_705_, 3);
v_toSeqRight_709_ = lean_ctor_get(v_toApplicative_705_, 4);
v___f_710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_711_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_706_, 2);
v___f_712_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_712_, 0, v_toFunctor_706_);
v___f_713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_713_, 0, v_toFunctor_706_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___f_712_);
lean_ctor_set(v___x_714_, 1, v___f_713_);
lean_inc(v_toSeqRight_709_);
v___f_715_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_715_, 0, v_toSeqRight_709_);
lean_inc(v_toSeqLeft_708_);
v___f_716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_716_, 0, v_toSeqLeft_708_);
lean_inc(v_toSeq_707_);
v___f_717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_717_, 0, v_toSeq_707_);
v___x_718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_718_, 0, v___x_714_);
lean_ctor_set(v___x_718_, 1, v___f_710_);
lean_ctor_set(v___x_718_, 2, v___f_717_);
lean_ctor_set(v___x_718_, 3, v___f_716_);
lean_ctor_set(v___x_718_, 4, v___f_715_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___f_711_);
v___x_720_ = l_StateRefT_x27_instMonad___redArg(v___x_719_);
v_toApplicative_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_720_, 1);
lean_dec(v_unused_776_);
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_775_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_toApplicative_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_775_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_toFunctor_725_; lean_object* v_toSeq_726_; lean_object* v_toSeqLeft_727_; lean_object* v_toSeqRight_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_773_; 
v_toFunctor_725_ = lean_ctor_get(v_toApplicative_721_, 0);
v_toSeq_726_ = lean_ctor_get(v_toApplicative_721_, 2);
v_toSeqLeft_727_ = lean_ctor_get(v_toApplicative_721_, 3);
v_toSeqRight_728_ = lean_ctor_get(v_toApplicative_721_, 4);
v_isSharedCheck_773_ = !lean_is_exclusive(v_toApplicative_721_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_toApplicative_721_, 1);
lean_dec(v_unused_774_);
v___x_730_ = v_toApplicative_721_;
v_isShared_731_ = v_isSharedCheck_773_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_toSeqRight_728_);
lean_inc(v_toSeqLeft_727_);
lean_inc(v_toSeq_726_);
lean_inc(v_toFunctor_725_);
lean_dec(v_toApplicative_721_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_773_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___f_732_; lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___f_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___x_741_; 
v___f_732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_725_);
v___f_734_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_734_, 0, v_toFunctor_725_);
v___f_735_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_735_, 0, v_toFunctor_725_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___f_734_);
lean_ctor_set(v___x_736_, 1, v___f_735_);
v___f_737_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_737_, 0, v_toSeqRight_728_);
v___f_738_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_738_, 0, v_toSeqLeft_727_);
v___f_739_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_739_, 0, v_toSeq_726_);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 4, v___f_737_);
lean_ctor_set(v___x_730_, 3, v___f_738_);
lean_ctor_set(v___x_730_, 2, v___f_739_);
lean_ctor_set(v___x_730_, 1, v___f_732_);
lean_ctor_set(v___x_730_, 0, v___x_736_);
v___x_741_ = v___x_730_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_736_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___f_732_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___f_739_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v___f_738_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v___f_737_);
v___x_741_ = v_reuseFailAlloc_772_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___f_733_);
lean_ctor_set(v___x_723_, 0, v___x_741_);
v___x_743_ = v___x_723_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___f_733_);
v___x_743_ = v_reuseFailAlloc_771_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_744_ = l_StateRefT_x27_instMonad___redArg(v___x_743_);
v___x_745_ = l_ReaderT_instMonad___redArg(v___x_744_);
v___x_746_ = l_StateRefT_x27_instMonad___redArg(v___x_745_);
v___x_747_ = l_ReaderT_instMonad___redArg(v___x_746_);
v___x_748_ = l_ReaderT_instMonad___redArg(v___x_747_);
v___x_749_ = l_StateRefT_x27_instMonad___redArg(v___x_748_);
v___x_750_ = l_ReaderT_instMonad___redArg(v___x_749_);
v___x_751_ = l_Lean_Meta_Grind_Order_getStruct(v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v_targets_753_; lean_object* v_size_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v_targets_753_ = lean_ctor_get(v_a_752_, 19);
lean_inc_ref(v_targets_753_);
lean_dec(v_a_752_);
v_size_754_ = lean_ctor_get(v_targets_753_, 2);
v___x_755_ = lean_box(0);
v___x_756_ = lean_nat_dec_lt(v_u_690_, v_size_754_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_804__overap_758_; lean_object* v___x_759_; 
lean_dec_ref(v_targets_753_);
v___x_757_ = l_outOfBounds___redArg(v___x_755_);
v___x_804__overap_758_ = l_Lean_AssocList_forM___redArg(v___x_750_, v_f_691_, v___x_757_);
lean_inc(v_a_702_);
lean_inc_ref(v_a_701_);
lean_inc(v_a_700_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc_ref(v_a_697_);
lean_inc(v_a_696_);
lean_inc_ref(v_a_695_);
lean_inc(v_a_694_);
lean_inc(v_a_693_);
lean_inc(v_a_692_);
v___x_759_ = lean_apply_12(v___x_804__overap_758_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_802__overap_761_; lean_object* v___x_762_; 
v___x_760_ = l_Lean_PersistentArray_get_x21___redArg(v___x_755_, v_targets_753_, v_u_690_);
lean_dec_ref(v_targets_753_);
v___x_802__overap_761_ = l_Lean_AssocList_forM___redArg(v___x_750_, v_f_691_, v___x_760_);
lean_inc(v_a_702_);
lean_inc_ref(v_a_701_);
lean_inc(v_a_700_);
lean_inc_ref(v_a_699_);
lean_inc(v_a_698_);
lean_inc_ref(v_a_697_);
lean_inc(v_a_696_);
lean_inc_ref(v_a_695_);
lean_inc(v_a_694_);
lean_inc(v_a_693_);
lean_inc(v_a_692_);
v___x_762_ = lean_apply_12(v___x_802__overap_761_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
return v___x_762_;
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___x_750_);
lean_dec_ref(v_f_691_);
v_a_763_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_751_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_751_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object* v_u_777_, lean_object* v_f_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(v_u_777_, v_f_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
lean_dec(v_a_780_);
lean_dec(v_a_779_);
lean_dec(v_u_777_);
return v_res_791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0(void){
_start:
{
uint8_t v___x_792_; lean_object* v___x_793_; 
v___x_792_ = 0;
v___x_793_ = l_Ordering_ctorIdx(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_794_, lean_object* v_v_795_, lean_object* v_k_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_794_, v_v_795_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_828_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_828_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_828_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (lean_obj_tag(v_a_810_) == 1)
{
lean_object* v_val_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v_val_814_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_a_810_, 1);
v___x_815_ = l_Lean_Meta_Grind_Order_Weight_compare(v_k_796_, v_val_814_);
lean_dec(v_val_814_);
v___x_816_ = l_Ordering_ctorIdx(v___x_815_);
v___x_817_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___closed__0);
v___x_818_ = lean_nat_dec_eq(v___x_816_, v___x_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(v___x_818_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; 
lean_dec(v_a_810_);
v___x_823_ = 1;
v___x_824_ = lean_box(v___x_823_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_824_);
v___x_826_ = v___x_812_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_809_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_809_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_837_, lean_object* v_v_838_, lean_object* v_k_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_837_, v_v_838_, v_k_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_k_839_);
lean_dec(v_v_838_);
lean_dec(v_u_837_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_853_, lean_object* v_s_854_){
_start:
{
lean_object* v_id_855_; lean_object* v_type_856_; lean_object* v_u_857_; lean_object* v_isPreorderInst_858_; lean_object* v_leInst_859_; lean_object* v_ltInst_x3f_860_; lean_object* v_isPartialInst_x3f_861_; lean_object* v_isLinearPreInst_x3f_862_; lean_object* v_lawfulOrderLTInst_x3f_863_; lean_object* v_ringId_x3f_864_; uint8_t v_isCommRing_865_; lean_object* v_ringInst_x3f_866_; lean_object* v_orderedRingInst_x3f_867_; lean_object* v_leFn_868_; lean_object* v_ltFn_x3f_869_; lean_object* v_nodes_870_; lean_object* v_nodeMap_871_; lean_object* v_cnstrs_872_; lean_object* v_cnstrsOf_873_; lean_object* v_sources_874_; lean_object* v_targets_875_; lean_object* v_proofs_876_; lean_object* v_propagate_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_885_; 
v_id_855_ = lean_ctor_get(v_s_854_, 0);
v_type_856_ = lean_ctor_get(v_s_854_, 1);
v_u_857_ = lean_ctor_get(v_s_854_, 2);
v_isPreorderInst_858_ = lean_ctor_get(v_s_854_, 3);
v_leInst_859_ = lean_ctor_get(v_s_854_, 4);
v_ltInst_x3f_860_ = lean_ctor_get(v_s_854_, 5);
v_isPartialInst_x3f_861_ = lean_ctor_get(v_s_854_, 6);
v_isLinearPreInst_x3f_862_ = lean_ctor_get(v_s_854_, 7);
v_lawfulOrderLTInst_x3f_863_ = lean_ctor_get(v_s_854_, 8);
v_ringId_x3f_864_ = lean_ctor_get(v_s_854_, 9);
v_isCommRing_865_ = lean_ctor_get_uint8(v_s_854_, sizeof(void*)*22);
v_ringInst_x3f_866_ = lean_ctor_get(v_s_854_, 10);
v_orderedRingInst_x3f_867_ = lean_ctor_get(v_s_854_, 11);
v_leFn_868_ = lean_ctor_get(v_s_854_, 12);
v_ltFn_x3f_869_ = lean_ctor_get(v_s_854_, 13);
v_nodes_870_ = lean_ctor_get(v_s_854_, 14);
v_nodeMap_871_ = lean_ctor_get(v_s_854_, 15);
v_cnstrs_872_ = lean_ctor_get(v_s_854_, 16);
v_cnstrsOf_873_ = lean_ctor_get(v_s_854_, 17);
v_sources_874_ = lean_ctor_get(v_s_854_, 18);
v_targets_875_ = lean_ctor_get(v_s_854_, 19);
v_proofs_876_ = lean_ctor_get(v_s_854_, 20);
v_propagate_877_ = lean_ctor_get(v_s_854_, 21);
v_isSharedCheck_885_ = !lean_is_exclusive(v_s_854_);
if (v_isSharedCheck_885_ == 0)
{
v___x_879_ = v_s_854_;
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_propagate_877_);
lean_inc(v_proofs_876_);
lean_inc(v_targets_875_);
lean_inc(v_sources_874_);
lean_inc(v_cnstrsOf_873_);
lean_inc(v_cnstrs_872_);
lean_inc(v_nodeMap_871_);
lean_inc(v_nodes_870_);
lean_inc(v_ltFn_x3f_869_);
lean_inc(v_leFn_868_);
lean_inc(v_orderedRingInst_x3f_867_);
lean_inc(v_ringInst_x3f_866_);
lean_inc(v_ringId_x3f_864_);
lean_inc(v_lawfulOrderLTInst_x3f_863_);
lean_inc(v_isLinearPreInst_x3f_862_);
lean_inc(v_isPartialInst_x3f_861_);
lean_inc(v_ltInst_x3f_860_);
lean_inc(v_leInst_859_);
lean_inc(v_isPreorderInst_858_);
lean_inc(v_u_857_);
lean_inc(v_type_856_);
lean_inc(v_id_855_);
lean_dec(v_s_854_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_885_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v_p_853_);
lean_ctor_set(v___x_881_, 1, v_propagate_877_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 21, v___x_881_);
v___x_883_ = v___x_879_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_id_855_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_type_856_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_u_857_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_isPreorderInst_858_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_leInst_859_);
lean_ctor_set(v_reuseFailAlloc_884_, 5, v_ltInst_x3f_860_);
lean_ctor_set(v_reuseFailAlloc_884_, 6, v_isPartialInst_x3f_861_);
lean_ctor_set(v_reuseFailAlloc_884_, 7, v_isLinearPreInst_x3f_862_);
lean_ctor_set(v_reuseFailAlloc_884_, 8, v_lawfulOrderLTInst_x3f_863_);
lean_ctor_set(v_reuseFailAlloc_884_, 9, v_ringId_x3f_864_);
lean_ctor_set(v_reuseFailAlloc_884_, 10, v_ringInst_x3f_866_);
lean_ctor_set(v_reuseFailAlloc_884_, 11, v_orderedRingInst_x3f_867_);
lean_ctor_set(v_reuseFailAlloc_884_, 12, v_leFn_868_);
lean_ctor_set(v_reuseFailAlloc_884_, 13, v_ltFn_x3f_869_);
lean_ctor_set(v_reuseFailAlloc_884_, 14, v_nodes_870_);
lean_ctor_set(v_reuseFailAlloc_884_, 15, v_nodeMap_871_);
lean_ctor_set(v_reuseFailAlloc_884_, 16, v_cnstrs_872_);
lean_ctor_set(v_reuseFailAlloc_884_, 17, v_cnstrsOf_873_);
lean_ctor_set(v_reuseFailAlloc_884_, 18, v_sources_874_);
lean_ctor_set(v_reuseFailAlloc_884_, 19, v_targets_875_);
lean_ctor_set(v_reuseFailAlloc_884_, 20, v_proofs_876_);
lean_ctor_set(v_reuseFailAlloc_884_, 21, v___x_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_884_, sizeof(void*)*22, v_isCommRing_865_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object* v_msgData_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; lean_object* v_mctx_895_; lean_object* v_lctx_896_; lean_object* v_options_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_892_ = lean_st_ref_get(v___y_890_);
v_env_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_892_);
v___x_894_ = lean_st_ref_get(v___y_888_);
v_mctx_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_895_);
lean_dec(v___x_894_);
v_lctx_896_ = lean_ctor_get(v___y_887_, 2);
v_options_897_ = lean_ctor_get(v___y_889_, 2);
lean_inc_ref(v_options_897_);
lean_inc_ref(v_lctx_896_);
v___x_898_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_898_, 0, v_env_893_);
lean_ctor_set(v___x_898_, 1, v_mctx_895_);
lean_ctor_set(v___x_898_, 2, v_lctx_896_);
lean_ctor_set(v___x_898_, 3, v_options_897_);
v___x_899_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
lean_ctor_set(v___x_899_, 1, v_msgData_886_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_908_; double v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_float_of_nat(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_ref_920_; lean_object* v___x_921_; lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_966_; 
v_ref_920_ = lean_ctor_get(v___y_917_, 5);
v___x_921_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
v_a_922_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_966_ == 0)
{
v___x_924_ = v___x_921_;
v_isShared_925_ = v_isSharedCheck_966_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_921_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_966_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v_traceState_927_; lean_object* v_env_928_; lean_object* v_nextMacroScope_929_; lean_object* v_ngen_930_; lean_object* v_auxDeclNGen_931_; lean_object* v_cache_932_; lean_object* v_messages_933_; lean_object* v_infoState_934_; lean_object* v_snapshotTasks_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_965_; 
v___x_926_ = lean_st_ref_take(v___y_918_);
v_traceState_927_ = lean_ctor_get(v___x_926_, 4);
v_env_928_ = lean_ctor_get(v___x_926_, 0);
v_nextMacroScope_929_ = lean_ctor_get(v___x_926_, 1);
v_ngen_930_ = lean_ctor_get(v___x_926_, 2);
v_auxDeclNGen_931_ = lean_ctor_get(v___x_926_, 3);
v_cache_932_ = lean_ctor_get(v___x_926_, 5);
v_messages_933_ = lean_ctor_get(v___x_926_, 6);
v_infoState_934_ = lean_ctor_get(v___x_926_, 7);
v_snapshotTasks_935_ = lean_ctor_get(v___x_926_, 8);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_965_ == 0)
{
v___x_937_ = v___x_926_;
v_isShared_938_ = v_isSharedCheck_965_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_snapshotTasks_935_);
lean_inc(v_infoState_934_);
lean_inc(v_messages_933_);
lean_inc(v_cache_932_);
lean_inc(v_traceState_927_);
lean_inc(v_auxDeclNGen_931_);
lean_inc(v_ngen_930_);
lean_inc(v_nextMacroScope_929_);
lean_inc(v_env_928_);
lean_dec(v___x_926_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_965_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
uint64_t v_tid_939_; lean_object* v_traces_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_964_; 
v_tid_939_ = lean_ctor_get_uint64(v_traceState_927_, sizeof(void*)*1);
v_traces_940_ = lean_ctor_get(v_traceState_927_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v_traceState_927_);
if (v_isSharedCheck_964_ == 0)
{
v___x_942_ = v_traceState_927_;
v_isShared_943_ = v_isSharedCheck_964_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_traces_940_);
lean_dec(v_traceState_927_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_964_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; double v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_944_ = lean_box(0);
v___x_945_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_946_ = 0;
v___x_947_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_948_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_948_, 0, v_cls_913_);
lean_ctor_set(v___x_948_, 1, v___x_944_);
lean_ctor_set(v___x_948_, 2, v___x_947_);
lean_ctor_set_float(v___x_948_, sizeof(void*)*3, v___x_945_);
lean_ctor_set_float(v___x_948_, sizeof(void*)*3 + 8, v___x_945_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*3 + 16, v___x_946_);
v___x_949_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_950_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v_a_922_);
lean_ctor_set(v___x_950_, 2, v___x_949_);
lean_inc(v_ref_920_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v_ref_920_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = l_Lean_PersistentArray_push___redArg(v_traces_940_, v___x_951_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v___x_952_);
v___x_954_ = v___x_942_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_952_);
lean_ctor_set_uint64(v_reuseFailAlloc_963_, sizeof(void*)*1, v_tid_939_);
v___x_954_ = v_reuseFailAlloc_963_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_956_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 4, v___x_954_);
v___x_956_ = v___x_937_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_env_928_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v_nextMacroScope_929_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_ngen_930_);
lean_ctor_set(v_reuseFailAlloc_962_, 3, v_auxDeclNGen_931_);
lean_ctor_set(v_reuseFailAlloc_962_, 4, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_962_, 5, v_cache_932_);
lean_ctor_set(v_reuseFailAlloc_962_, 6, v_messages_933_);
lean_ctor_set(v_reuseFailAlloc_962_, 7, v_infoState_934_);
lean_ctor_set(v_reuseFailAlloc_962_, 8, v_snapshotTasks_935_);
v___x_956_ = v_reuseFailAlloc_962_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_957_ = lean_st_ref_put(v___y_918_, v___x_956_);
v___x_958_ = lean_box(0);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_958_);
v___x_960_ = v___x_924_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_967_, lean_object* v_msg_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_967_, v_msg_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_cls_987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_989_ = l_Lean_Name_append(v___x_988_, v_cls_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_options_1003_; lean_object* v_inheritedTraceOptions_1004_; uint8_t v_hasTrace_1005_; lean_object* v___f_1006_; 
v_options_1003_ = lean_ctor_get(v_a_1000_, 2);
v_inheritedTraceOptions_1004_ = lean_ctor_get(v_a_1000_, 13);
v_hasTrace_1005_ = lean_ctor_get_uint8(v_options_1003_, sizeof(void*)*1);
lean_inc_ref(v_p_990_);
v___f_1006_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_1006_, 0, v_p_990_);
if (v_hasTrace_1005_ == 0)
{
lean_object* v___x_1007_; 
lean_dec_ref(v_p_990_);
v___x_1007_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1006_, v_a_991_, v_a_992_);
return v___x_1007_;
}
else
{
lean_object* v_cls_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v_cls_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7);
v___x_1010_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1004_, v_options_1003_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec_ref(v_p_990_);
v___x_1011_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1006_, v_a_991_, v_a_992_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_p_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v___x_1014_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1008_, v_a_1013_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1015_; 
lean_dec_ref_known(v___x_1014_, 1);
v___x_1015_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1006_, v_a_991_, v_a_992_);
return v___x_1015_;
}
else
{
lean_dec_ref(v___f_1006_);
return v___x_1014_;
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref(v___f_1006_);
v_a_1016_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1012_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1012_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_1038_, lean_object* v_msg_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1038_, v_msg_1039_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_1053_, lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1053_, v_msg_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec(v___y_1055_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1068_, lean_object* v_vals_1069_, lean_object* v_i_1070_, lean_object* v_k_1071_){
_start:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_array_get_size(v_keys_1068_);
v___x_1073_ = lean_nat_dec_lt(v_i_1070_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v_i_1070_);
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
else
{
lean_object* v_k_x27_1075_; size_t v___x_1076_; size_t v___x_1077_; uint8_t v___x_1078_; 
v_k_x27_1075_ = lean_array_fget_borrowed(v_keys_1068_, v_i_1070_);
v___x_1076_ = lean_ptr_addr(v_k_1071_);
v___x_1077_ = lean_ptr_addr(v_k_x27_1075_);
v___x_1078_ = lean_usize_dec_eq(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_i_1070_, v___x_1079_);
lean_dec(v_i_1070_);
v_i_1070_ = v___x_1080_;
goto _start;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_array_fget_borrowed(v_vals_1069_, v_i_1070_);
lean_dec(v_i_1070_);
lean_inc(v___x_1082_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_i_1086_, lean_object* v_k_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1084_, v_vals_1085_, v_i_1086_, v_k_1087_);
lean_dec_ref(v_k_1087_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1089_, size_t v_x_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1089_) == 0)
{
lean_object* v_es_1092_; lean_object* v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v_j_1096_; lean_object* v___x_1097_; 
v_es_1092_ = lean_ctor_get(v_x_1089_, 0);
v___x_1093_ = lean_box(2);
v___x_1094_ = ((size_t)31ULL);
v___x_1095_ = lean_usize_land(v_x_1090_, v___x_1094_);
v_j_1096_ = lean_usize_to_nat(v___x_1095_);
v___x_1097_ = lean_array_get_borrowed(v___x_1093_, v_es_1092_, v_j_1096_);
lean_dec(v_j_1096_);
switch(lean_obj_tag(v___x_1097_))
{
case 0:
{
lean_object* v_key_1098_; lean_object* v_val_1099_; size_t v___x_1100_; size_t v___x_1101_; uint8_t v___x_1102_; 
v_key_1098_ = lean_ctor_get(v___x_1097_, 0);
v_val_1099_ = lean_ctor_get(v___x_1097_, 1);
v___x_1100_ = lean_ptr_addr(v_x_1091_);
v___x_1101_ = lean_ptr_addr(v_key_1098_);
v___x_1102_ = lean_usize_dec_eq(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; 
lean_inc(v_val_1099_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_val_1099_);
return v___x_1104_;
}
}
case 1:
{
lean_object* v_node_1105_; size_t v___x_1106_; size_t v___x_1107_; 
v_node_1105_ = lean_ctor_get(v___x_1097_, 0);
v___x_1106_ = ((size_t)5ULL);
v___x_1107_ = lean_usize_shift_right(v_x_1090_, v___x_1106_);
v_x_1089_ = v_node_1105_;
v_x_1090_ = v___x_1107_;
goto _start;
}
default: 
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
}
}
else
{
lean_object* v_ks_1110_; lean_object* v_vs_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v_ks_1110_ = lean_ctor_get(v_x_1089_, 0);
v_vs_1111_ = lean_ctor_get(v_x_1089_, 1);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1110_, v_vs_1111_, v___x_1112_, v_x_1091_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
size_t v_x_9896__boxed_1117_; lean_object* v_res_1118_; 
v_x_9896__boxed_1117_ = lean_unbox_usize(v_x_1115_);
lean_dec(v_x_1115_);
v_res_1118_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1114_, v_x_9896__boxed_1117_, v_x_1116_);
lean_dec_ref(v_x_1116_);
lean_dec_ref(v_x_1114_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
size_t v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; uint64_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1121_ = lean_ptr_addr(v_x_1120_);
v___x_1122_ = ((size_t)3ULL);
v___x_1123_ = lean_usize_shift_right(v___x_1121_, v___x_1122_);
v___x_1124_ = lean_usize_to_uint64(v___x_1123_);
v___x_1125_ = lean_uint64_to_usize(v___x_1124_);
v___x_1126_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1119_, v___x_1125_, v_x_1120_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1127_, v_x_1128_);
lean_dec_ref(v_x_1128_);
lean_dec_ref(v_x_1127_);
return v_res_1129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1141_ = l_Lean_mkConst(v___x_1140_, v___x_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1142_, lean_object* v_e_1143_, lean_object* v_u_1144_, lean_object* v_v_1145_, lean_object* v_k_1146_, lean_object* v_k_x27_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v_h_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1144_, v_v_1145_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1144_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1145_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1191_, v_a_1193_, v_k_1146_, v_a_1189_, v_k_x27_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_h_x3f_1195_; 
v_h_x3f_1195_ = lean_ctor_get(v_c_1142_, 4);
lean_inc(v_h_x3f_1195_);
if (lean_obj_tag(v_h_x3f_1195_) == 1)
{
lean_object* v_a_1196_; lean_object* v_e_1197_; lean_object* v_val_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_a_1196_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1194_, 1);
v_e_1197_ = lean_ctor_get(v_c_1142_, 3);
lean_inc_ref(v_e_1197_);
lean_dec_ref(v_c_1142_);
v_val_1198_ = lean_ctor_get(v_h_x3f_1195_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_h_x3f_1195_, 1);
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1143_);
v___x_1200_ = l_Lean_mkApp4(v___x_1199_, v_e_1143_, v_e_1197_, v_val_1198_, v_a_1196_);
v_h_1161_ = v___x_1200_;
v___y_1162_ = v_a_1149_;
v___y_1163_ = v_a_1151_;
v___y_1164_ = v_a_1153_;
v___y_1165_ = v_a_1155_;
v___y_1166_ = v_a_1156_;
v___y_1167_ = v_a_1157_;
v___y_1168_ = v_a_1158_;
goto v___jp_1160_;
}
else
{
lean_object* v_a_1201_; 
lean_dec(v_h_x3f_1195_);
lean_dec_ref(v_c_1142_);
v_a_1201_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1201_);
lean_dec_ref_known(v___x_1194_, 1);
v_h_1161_ = v_a_1201_;
v___y_1162_ = v_a_1149_;
v___y_1163_ = v_a_1151_;
v___y_1164_ = v_a_1153_;
v___y_1165_ = v_a_1155_;
v___y_1166_ = v_a_1156_;
v___y_1167_ = v_a_1157_;
v___y_1168_ = v_a_1158_;
goto v___jp_1160_;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_e_1143_);
lean_dec_ref(v_c_1142_);
v_a_1202_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1194_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1194_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_a_1191_);
lean_dec(v_a_1189_);
lean_dec_ref(v_e_1143_);
lean_dec_ref(v_c_1142_);
v_a_1210_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1192_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1192_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_a_1189_);
lean_dec_ref(v_e_1143_);
lean_dec_ref(v_c_1142_);
v_a_1218_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1190_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1190_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_e_1143_);
lean_dec_ref(v_c_1142_);
v_a_1226_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1188_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1188_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
v___jp_1160_:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1162_, v___y_1167_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v_termMapInv_1171_; lean_object* v___x_1172_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v_termMapInv_1171_ = lean_ctor_get(v_a_1170_, 4);
lean_inc_ref(v_termMapInv_1171_);
lean_dec(v_a_1170_);
v___x_1172_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1171_, v_e_1143_);
lean_dec_ref(v_termMapInv_1171_);
if (lean_obj_tag(v___x_1172_) == 1)
{
lean_object* v_val_1173_; lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v_fst_1174_ = lean_ctor_get(v_val_1173_, 0);
lean_inc_n(v_fst_1174_, 2);
v_snd_1175_ = lean_ctor_get(v_val_1173_, 1);
lean_inc(v_snd_1175_);
lean_dec(v_val_1173_);
v___x_1176_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1177_ = l_Lean_mkApp4(v___x_1176_, v_fst_1174_, v_e_1143_, v_snd_1175_, v_h_1161_);
v___x_1178_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1174_, v___x_1177_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
lean_dec(v___x_1172_);
v___x_1179_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1143_, v_h_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1179_;
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_h_1161_);
lean_dec_ref(v_e_1143_);
v_a_1180_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1169_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1169_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1234_ = _args[0];
lean_object* v_e_1235_ = _args[1];
lean_object* v_u_1236_ = _args[2];
lean_object* v_v_1237_ = _args[3];
lean_object* v_k_1238_ = _args[4];
lean_object* v_k_x27_1239_ = _args[5];
lean_object* v_a_1240_ = _args[6];
lean_object* v_a_1241_ = _args[7];
lean_object* v_a_1242_ = _args[8];
lean_object* v_a_1243_ = _args[9];
lean_object* v_a_1244_ = _args[10];
lean_object* v_a_1245_ = _args[11];
lean_object* v_a_1246_ = _args[12];
lean_object* v_a_1247_ = _args[13];
lean_object* v_a_1248_ = _args[14];
lean_object* v_a_1249_ = _args[15];
lean_object* v_a_1250_ = _args[16];
lean_object* v_a_1251_ = _args[17];
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1234_, v_e_1235_, v_u_1236_, v_v_1237_, v_k_1238_, v_k_x27_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_k_x27_1239_);
lean_dec_ref(v_k_1238_);
lean_dec(v_v_1237_);
lean_dec(v_u_1236_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1254_, v_x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1257_, v_x_1258_, v_x_1259_);
lean_dec_ref(v_x_1259_);
lean_dec_ref(v_x_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, size_t v_x_1263_, lean_object* v_x_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1262_, v_x_1263_, v_x_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
size_t v_x_10164__boxed_1270_; lean_object* v_res_1271_; 
v_x_10164__boxed_1270_ = lean_unbox_usize(v_x_1268_);
lean_dec(v_x_1268_);
v_res_1271_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1266_, v_x_1267_, v_x_10164__boxed_1270_, v_x_1269_);
lean_dec_ref(v_x_1269_);
lean_dec_ref(v_x_1267_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1272_, lean_object* v_keys_1273_, lean_object* v_vals_1274_, lean_object* v_heq_1275_, lean_object* v_i_1276_, lean_object* v_k_1277_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1273_, v_vals_1274_, v_i_1276_, v_k_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_heq_1282_, lean_object* v_i_1283_, lean_object* v_k_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1279_, v_keys_1280_, v_vals_1281_, v_heq_1282_, v_i_1283_, v_k_1284_);
lean_dec_ref(v_k_1284_);
lean_dec_ref(v_vals_1281_);
lean_dec_ref(v_keys_1280_);
return v_res_1285_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___x_5398__overap_1302_; lean_object* v___x_1303_; 
v___x_1300_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1301_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1301_, 0, v___x_1300_);
v___x_5398__overap_1302_ = lean_panic_fn_borrowed(v___f_1301_, v_msg_1287_);
lean_dec_ref(v___f_1301_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc(v___y_1288_);
v___x_1303_ = lean_apply_12(v___x_5398__overap_1302_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, lean_box(0));
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec(v___y_1305_);
return v_res_1317_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1321_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1322_ = lean_unsigned_to_nat(2u);
v___x_1323_ = lean_unsigned_to_nat(86u);
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1326_ = l_mkPanicMessageWithDecl(v___x_1325_, v___x_1324_, v___x_1323_, v___x_1322_, v___x_1321_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_u_1341_; lean_object* v_v_1342_; lean_object* v_e_1343_; lean_object* v_h_x3f_1344_; lean_object* v___x_1345_; 
v_u_1341_ = lean_ctor_get(v_c_1327_, 0);
v_v_1342_ = lean_ctor_get(v_c_1327_, 1);
v_e_1343_ = lean_ctor_get(v_c_1327_, 3);
lean_inc_ref(v_e_1343_);
v_h_x3f_1344_ = lean_ctor_get(v_c_1327_, 4);
lean_inc(v_h_x3f_1344_);
v___x_1345_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1341_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; uint8_t v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = lean_nat_dec_eq(v_u_1341_, v_v_1342_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_a_1346_);
lean_dec(v_h_x3f_1344_);
lean_dec_ref(v_e_1343_);
lean_dec_ref(v_e_1328_);
lean_dec_ref(v_c_1327_);
v___x_1348_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1349_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1348_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1349_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1327_);
lean_dec_ref(v_c_1327_);
v___x_1351_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1346_, v___x_1350_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec_ref(v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_h_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
if (lean_obj_tag(v_h_x3f_1344_) == 1)
{
lean_object* v_val_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_val_1381_ = lean_ctor_get(v_h_x3f_1344_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v_h_x3f_1344_, 1);
v___x_1382_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1328_);
v___x_1383_ = l_Lean_mkApp4(v___x_1382_, v_e_1328_, v_e_1343_, v_val_1381_, v_a_1352_);
v_h_1354_ = v___x_1383_;
v___y_1355_ = v_a_1330_;
v___y_1356_ = v_a_1332_;
v___y_1357_ = v_a_1334_;
v___y_1358_ = v_a_1336_;
v___y_1359_ = v_a_1337_;
v___y_1360_ = v_a_1338_;
v___y_1361_ = v_a_1339_;
goto v___jp_1353_;
}
else
{
lean_dec(v_h_x3f_1344_);
lean_dec_ref(v_e_1343_);
v_h_1354_ = v_a_1352_;
v___y_1355_ = v_a_1330_;
v___y_1356_ = v_a_1332_;
v___y_1357_ = v_a_1334_;
v___y_1358_ = v_a_1336_;
v___y_1359_ = v_a_1337_;
v___y_1360_ = v_a_1338_;
v___y_1361_ = v_a_1339_;
goto v___jp_1353_;
}
v___jp_1353_:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1355_, v___y_1360_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v_termMapInv_1364_; lean_object* v___x_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v_termMapInv_1364_ = lean_ctor_get(v_a_1363_, 4);
lean_inc_ref(v_termMapInv_1364_);
lean_dec(v_a_1363_);
v___x_1365_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1364_, v_e_1328_);
lean_dec_ref(v_termMapInv_1364_);
if (lean_obj_tag(v___x_1365_) == 1)
{
lean_object* v_val_1366_; lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v_val_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v_fst_1367_ = lean_ctor_get(v_val_1366_, 0);
lean_inc_n(v_fst_1367_, 2);
v_snd_1368_ = lean_ctor_get(v_val_1366_, 1);
lean_inc(v_snd_1368_);
lean_dec(v_val_1366_);
v___x_1369_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1370_ = l_Lean_mkApp4(v___x_1369_, v_fst_1367_, v_e_1328_, v_snd_1368_, v_h_1354_);
v___x_1371_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1367_, v___x_1370_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; 
lean_dec(v___x_1365_);
v___x_1372_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1328_, v_h_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1372_;
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec_ref(v_h_1354_);
lean_dec_ref(v_e_1328_);
v_a_1373_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1362_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1362_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v_h_x3f_1344_);
lean_dec_ref(v_e_1343_);
lean_dec_ref(v_e_1328_);
v_a_1384_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1351_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1351_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_h_x3f_1344_);
lean_dec_ref(v_e_1343_);
lean_dec_ref(v_e_1328_);
lean_dec_ref(v_c_1327_);
v_a_1392_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1345_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1345_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1400_, lean_object* v_e_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1400_, v_e_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec(v_a_1402_);
return v_res_1414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1423_ = l_Lean_mkConst(v___x_1422_, v___x_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1424_, lean_object* v_e_1425_, lean_object* v_u_1426_, lean_object* v_v_1427_, lean_object* v_k_1428_, lean_object* v_k_x27_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_h_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1426_, v_v_1427_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
v___x_1472_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1426_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1427_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1473_, v_a_1475_, v_k_1428_, v_a_1471_, v_k_x27_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_h_x3f_1477_; 
v_h_x3f_1477_ = lean_ctor_get(v_c_1424_, 4);
lean_inc(v_h_x3f_1477_);
if (lean_obj_tag(v_h_x3f_1477_) == 1)
{
lean_object* v_a_1478_; lean_object* v_e_1479_; lean_object* v_val_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v_a_1478_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1476_, 1);
v_e_1479_ = lean_ctor_get(v_c_1424_, 3);
lean_inc_ref(v_e_1479_);
lean_dec_ref(v_c_1424_);
v_val_1480_ = lean_ctor_get(v_h_x3f_1477_, 0);
lean_inc(v_val_1480_);
lean_dec_ref_known(v_h_x3f_1477_, 1);
v___x_1481_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1425_);
v___x_1482_ = l_Lean_mkApp4(v___x_1481_, v_e_1425_, v_e_1479_, v_val_1480_, v_a_1478_);
v_h_1443_ = v___x_1482_;
v___y_1444_ = v_a_1431_;
v___y_1445_ = v_a_1433_;
v___y_1446_ = v_a_1435_;
v___y_1447_ = v_a_1437_;
v___y_1448_ = v_a_1438_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
goto v___jp_1442_;
}
else
{
lean_object* v_a_1483_; 
lean_dec(v_h_x3f_1477_);
lean_dec_ref(v_c_1424_);
v_a_1483_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1476_, 1);
v_h_1443_ = v_a_1483_;
v___y_1444_ = v_a_1431_;
v___y_1445_ = v_a_1433_;
v___y_1446_ = v_a_1435_;
v___y_1447_ = v_a_1437_;
v___y_1448_ = v_a_1438_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
goto v___jp_1442_;
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v_e_1425_);
lean_dec_ref(v_c_1424_);
v_a_1484_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1476_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1476_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v_a_1473_);
lean_dec(v_a_1471_);
lean_dec_ref(v_e_1425_);
lean_dec_ref(v_c_1424_);
v_a_1492_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1474_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1474_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_a_1471_);
lean_dec_ref(v_e_1425_);
lean_dec_ref(v_c_1424_);
v_a_1500_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1472_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1472_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec_ref(v_e_1425_);
lean_dec_ref(v_c_1424_);
v_a_1508_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1470_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1470_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1444_, v___y_1449_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v_termMapInv_1453_; lean_object* v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v_termMapInv_1453_ = lean_ctor_get(v_a_1452_, 4);
lean_inc_ref(v_termMapInv_1453_);
lean_dec(v_a_1452_);
v___x_1454_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1453_, v_e_1425_);
lean_dec_ref(v_termMapInv_1453_);
if (lean_obj_tag(v___x_1454_) == 1)
{
lean_object* v_val_1455_; lean_object* v_fst_1456_; lean_object* v_snd_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v_val_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_fst_1456_ = lean_ctor_get(v_val_1455_, 0);
lean_inc_n(v_fst_1456_, 2);
v_snd_1457_ = lean_ctor_get(v_val_1455_, 1);
lean_inc(v_snd_1457_);
lean_dec(v_val_1455_);
v___x_1458_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1459_ = l_Lean_mkApp4(v___x_1458_, v_fst_1456_, v_e_1425_, v_snd_1457_, v_h_1443_);
v___x_1460_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1456_, v___x_1459_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; 
lean_dec(v___x_1454_);
v___x_1461_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1425_, v_h_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1461_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v_h_1443_);
lean_dec_ref(v_e_1425_);
v_a_1462_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1451_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1451_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1467_; 
if (v_isShared_1465_ == 0)
{
v___x_1467_ = v___x_1464_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_a_1462_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1516_ = _args[0];
lean_object* v_e_1517_ = _args[1];
lean_object* v_u_1518_ = _args[2];
lean_object* v_v_1519_ = _args[3];
lean_object* v_k_1520_ = _args[4];
lean_object* v_k_x27_1521_ = _args[5];
lean_object* v_a_1522_ = _args[6];
lean_object* v_a_1523_ = _args[7];
lean_object* v_a_1524_ = _args[8];
lean_object* v_a_1525_ = _args[9];
lean_object* v_a_1526_ = _args[10];
lean_object* v_a_1527_ = _args[11];
lean_object* v_a_1528_ = _args[12];
lean_object* v_a_1529_ = _args[13];
lean_object* v_a_1530_ = _args[14];
lean_object* v_a_1531_ = _args[15];
lean_object* v_a_1532_ = _args[16];
lean_object* v_a_1533_ = _args[17];
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1516_, v_e_1517_, v_u_1518_, v_v_1519_, v_k_1520_, v_k_x27_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_k_x27_1521_);
lean_dec_ref(v_k_1520_);
lean_dec(v_v_1519_);
lean_dec(v_u_1518_);
return v_res_1534_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1536_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1537_ = lean_unsigned_to_nat(2u);
v___x_1538_ = lean_unsigned_to_nat(111u);
v___x_1539_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1540_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1541_ = l_mkPanicMessageWithDecl(v___x_1540_, v___x_1539_, v___x_1538_, v___x_1537_, v___x_1536_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1542_, lean_object* v_e_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_u_1556_; lean_object* v_v_1557_; lean_object* v_e_1558_; lean_object* v_h_x3f_1559_; lean_object* v___x_1560_; 
v_u_1556_ = lean_ctor_get(v_c_1542_, 0);
v_v_1557_ = lean_ctor_get(v_c_1542_, 1);
v_e_1558_ = lean_ctor_get(v_c_1542_, 3);
lean_inc_ref(v_e_1558_);
v_h_x3f_1559_ = lean_ctor_get(v_c_1542_, 4);
lean_inc(v_h_x3f_1559_);
v___x_1560_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1556_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; uint8_t v___x_1562_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = lean_nat_dec_eq(v_u_1556_, v_v_1557_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec(v_a_1561_);
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v_e_1558_);
lean_dec_ref(v_e_1543_);
lean_dec_ref(v_c_1542_);
v___x_1563_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1564_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1563_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1542_);
lean_dec_ref(v_c_1542_);
v___x_1566_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1561_, v___x_1565_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_);
lean_dec_ref(v___x_1565_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v_h_1569_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
if (lean_obj_tag(v_h_x3f_1559_) == 1)
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_val_1596_ = lean_ctor_get(v_h_x3f_1559_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_h_x3f_1559_, 1);
v___x_1597_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1543_);
v___x_1598_ = l_Lean_mkApp4(v___x_1597_, v_e_1543_, v_e_1558_, v_val_1596_, v_a_1567_);
v_h_1569_ = v___x_1598_;
v___y_1570_ = v_a_1545_;
v___y_1571_ = v_a_1547_;
v___y_1572_ = v_a_1549_;
v___y_1573_ = v_a_1551_;
v___y_1574_ = v_a_1552_;
v___y_1575_ = v_a_1553_;
v___y_1576_ = v_a_1554_;
goto v___jp_1568_;
}
else
{
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v_e_1558_);
v_h_1569_ = v_a_1567_;
v___y_1570_ = v_a_1545_;
v___y_1571_ = v_a_1547_;
v___y_1572_ = v_a_1549_;
v___y_1573_ = v_a_1551_;
v___y_1574_ = v_a_1552_;
v___y_1575_ = v_a_1553_;
v___y_1576_ = v_a_1554_;
goto v___jp_1568_;
}
v___jp_1568_:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1570_, v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_termMapInv_1579_; lean_object* v___x_1580_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v_termMapInv_1579_ = lean_ctor_get(v_a_1578_, 4);
lean_inc_ref(v_termMapInv_1579_);
lean_dec(v_a_1578_);
v___x_1580_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1579_, v_e_1543_);
lean_dec_ref(v_termMapInv_1579_);
if (lean_obj_tag(v___x_1580_) == 1)
{
lean_object* v_val_1581_; lean_object* v_fst_1582_; lean_object* v_snd_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_val_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_val_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v_fst_1582_ = lean_ctor_get(v_val_1581_, 0);
lean_inc_n(v_fst_1582_, 2);
v_snd_1583_ = lean_ctor_get(v_val_1581_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_val_1581_);
v___x_1584_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1585_ = l_Lean_mkApp4(v___x_1584_, v_fst_1582_, v_e_1543_, v_snd_1583_, v_h_1569_);
v___x_1586_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1582_, v___x_1585_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; 
lean_dec(v___x_1580_);
v___x_1587_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1543_, v_h_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
return v___x_1587_;
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
lean_dec_ref(v_h_1569_);
lean_dec_ref(v_e_1543_);
v_a_1588_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1577_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1577_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v_e_1558_);
lean_dec_ref(v_e_1543_);
v_a_1599_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1566_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1566_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec(v_h_x3f_1559_);
lean_dec_ref(v_e_1558_);
lean_dec_ref(v_e_1543_);
lean_dec_ref(v_c_1542_);
v_a_1607_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1560_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1560_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1615_, lean_object* v_e_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1615_, v_e_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec(v_a_1617_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1631_, v_a_1632_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1644_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1644_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v_termMapInv_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v_termMapInv_1639_ = lean_ctor_get(v_a_1635_, 4);
lean_inc_ref(v_termMapInv_1639_);
lean_dec(v_a_1635_);
v___x_1640_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1639_, v_e_1630_);
lean_dec_ref(v_termMapInv_1639_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1634_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1634_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_e_1653_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1658_, v_a_1659_, v_a_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_e_1671_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1684_){
_start:
{
lean_object* v_id_1685_; lean_object* v_type_1686_; lean_object* v_u_1687_; lean_object* v_isPreorderInst_1688_; lean_object* v_leInst_1689_; lean_object* v_ltInst_x3f_1690_; lean_object* v_isPartialInst_x3f_1691_; lean_object* v_isLinearPreInst_x3f_1692_; lean_object* v_lawfulOrderLTInst_x3f_1693_; lean_object* v_ringId_x3f_1694_; uint8_t v_isCommRing_1695_; lean_object* v_ringInst_x3f_1696_; lean_object* v_orderedRingInst_x3f_1697_; lean_object* v_leFn_1698_; lean_object* v_ltFn_x3f_1699_; lean_object* v_nodes_1700_; lean_object* v_nodeMap_1701_; lean_object* v_cnstrs_1702_; lean_object* v_cnstrsOf_1703_; lean_object* v_sources_1704_; lean_object* v_targets_1705_; lean_object* v_proofs_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1714_; 
v_id_1685_ = lean_ctor_get(v_s_1684_, 0);
v_type_1686_ = lean_ctor_get(v_s_1684_, 1);
v_u_1687_ = lean_ctor_get(v_s_1684_, 2);
v_isPreorderInst_1688_ = lean_ctor_get(v_s_1684_, 3);
v_leInst_1689_ = lean_ctor_get(v_s_1684_, 4);
v_ltInst_x3f_1690_ = lean_ctor_get(v_s_1684_, 5);
v_isPartialInst_x3f_1691_ = lean_ctor_get(v_s_1684_, 6);
v_isLinearPreInst_x3f_1692_ = lean_ctor_get(v_s_1684_, 7);
v_lawfulOrderLTInst_x3f_1693_ = lean_ctor_get(v_s_1684_, 8);
v_ringId_x3f_1694_ = lean_ctor_get(v_s_1684_, 9);
v_isCommRing_1695_ = lean_ctor_get_uint8(v_s_1684_, sizeof(void*)*22);
v_ringInst_x3f_1696_ = lean_ctor_get(v_s_1684_, 10);
v_orderedRingInst_x3f_1697_ = lean_ctor_get(v_s_1684_, 11);
v_leFn_1698_ = lean_ctor_get(v_s_1684_, 12);
v_ltFn_x3f_1699_ = lean_ctor_get(v_s_1684_, 13);
v_nodes_1700_ = lean_ctor_get(v_s_1684_, 14);
v_nodeMap_1701_ = lean_ctor_get(v_s_1684_, 15);
v_cnstrs_1702_ = lean_ctor_get(v_s_1684_, 16);
v_cnstrsOf_1703_ = lean_ctor_get(v_s_1684_, 17);
v_sources_1704_ = lean_ctor_get(v_s_1684_, 18);
v_targets_1705_ = lean_ctor_get(v_s_1684_, 19);
v_proofs_1706_ = lean_ctor_get(v_s_1684_, 20);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_s_1684_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_s_1684_, 21);
lean_dec(v_unused_1715_);
v___x_1708_ = v_s_1684_;
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_proofs_1706_);
lean_inc(v_targets_1705_);
lean_inc(v_sources_1704_);
lean_inc(v_cnstrsOf_1703_);
lean_inc(v_cnstrs_1702_);
lean_inc(v_nodeMap_1701_);
lean_inc(v_nodes_1700_);
lean_inc(v_ltFn_x3f_1699_);
lean_inc(v_leFn_1698_);
lean_inc(v_orderedRingInst_x3f_1697_);
lean_inc(v_ringInst_x3f_1696_);
lean_inc(v_ringId_x3f_1694_);
lean_inc(v_lawfulOrderLTInst_x3f_1693_);
lean_inc(v_isLinearPreInst_x3f_1692_);
lean_inc(v_isPartialInst_x3f_1691_);
lean_inc(v_ltInst_x3f_1690_);
lean_inc(v_leInst_1689_);
lean_inc(v_isPreorderInst_1688_);
lean_inc(v_u_1687_);
lean_inc(v_type_1686_);
lean_inc(v_id_1685_);
lean_dec(v_s_1684_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1714_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
v___x_1710_ = lean_box(0);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 21, v___x_1710_);
v___x_1712_ = v___x_1708_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_id_1685_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_type_1686_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_u_1687_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_isPreorderInst_1688_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v_leInst_1689_);
lean_ctor_set(v_reuseFailAlloc_1713_, 5, v_ltInst_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1713_, 6, v_isPartialInst_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1713_, 7, v_isLinearPreInst_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1713_, 8, v_lawfulOrderLTInst_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1713_, 9, v_ringId_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1713_, 10, v_ringInst_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1713_, 11, v_orderedRingInst_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1713_, 12, v_leFn_1698_);
lean_ctor_set(v_reuseFailAlloc_1713_, 13, v_ltFn_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1713_, 14, v_nodes_1700_);
lean_ctor_set(v_reuseFailAlloc_1713_, 15, v_nodeMap_1701_);
lean_ctor_set(v_reuseFailAlloc_1713_, 16, v_cnstrs_1702_);
lean_ctor_set(v_reuseFailAlloc_1713_, 17, v_cnstrsOf_1703_);
lean_ctor_set(v_reuseFailAlloc_1713_, 18, v_sources_1704_);
lean_ctor_set(v_reuseFailAlloc_1713_, 19, v_targets_1705_);
lean_ctor_set(v_reuseFailAlloc_1713_, 20, v_proofs_1706_);
lean_ctor_set(v_reuseFailAlloc_1713_, 21, v___x_1710_);
lean_ctor_set_uint8(v_reuseFailAlloc_1713_, sizeof(void*)*22, v_isCommRing_1695_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1724_ = l_Lean_mkConst(v___x_1723_, v___x_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
if (lean_obj_tag(v_as_x27_1725_) == 0)
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v_b_1726_);
return v___x_1739_;
}
else
{
lean_object* v_head_1740_; lean_object* v_tail_1741_; lean_object* v___x_1742_; 
v_head_1740_ = lean_ctor_get(v_as_x27_1725_, 0);
v_tail_1741_ = lean_ctor_get(v_as_x27_1725_, 1);
v___x_1742_ = lean_box(0);
switch(lean_obj_tag(v_head_1740_))
{
case 0:
{
lean_object* v_c_1743_; lean_object* v_e_1744_; lean_object* v_u_1745_; lean_object* v_v_1746_; lean_object* v_k_1747_; lean_object* v_k_x27_1748_; lean_object* v___x_1749_; 
v_c_1743_ = lean_ctor_get(v_head_1740_, 0);
v_e_1744_ = lean_ctor_get(v_head_1740_, 1);
v_u_1745_ = lean_ctor_get(v_head_1740_, 2);
v_v_1746_ = lean_ctor_get(v_head_1740_, 3);
v_k_1747_ = lean_ctor_get(v_head_1740_, 4);
v_k_x27_1748_ = lean_ctor_get(v_head_1740_, 5);
lean_inc_ref(v_e_1744_);
lean_inc_ref(v_c_1743_);
v___x_1749_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1743_, v_e_1744_, v_u_1745_, v_v_1746_, v_k_1747_, v_k_x27_1748_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_dec_ref_known(v___x_1749_, 1);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
else
{
return v___x_1749_;
}
}
case 1:
{
lean_object* v_c_1751_; lean_object* v_e_1752_; lean_object* v_u_1753_; lean_object* v_v_1754_; lean_object* v_k_1755_; lean_object* v_k_x27_1756_; lean_object* v___x_1757_; 
v_c_1751_ = lean_ctor_get(v_head_1740_, 0);
v_e_1752_ = lean_ctor_get(v_head_1740_, 1);
v_u_1753_ = lean_ctor_get(v_head_1740_, 2);
v_v_1754_ = lean_ctor_get(v_head_1740_, 3);
v_k_1755_ = lean_ctor_get(v_head_1740_, 4);
v_k_x27_1756_ = lean_ctor_get(v_head_1740_, 5);
lean_inc_ref(v_e_1752_);
lean_inc_ref(v_c_1751_);
v___x_1757_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1751_, v_e_1752_, v_u_1753_, v_v_1754_, v_k_1755_, v_k_x27_1756_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_dec_ref_known(v___x_1757_, 1);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
else
{
return v___x_1757_;
}
}
default: 
{
lean_object* v_u_1759_; lean_object* v_v_1760_; lean_object* v___x_1761_; 
v_u_1759_ = lean_ctor_get(v_head_1740_, 0);
v_v_1760_ = lean_ctor_get(v_head_1740_, 1);
v___x_1761_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1759_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1760_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1898_; lean_object* v___x_1952_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1952_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1762_, v___y_1728_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; uint8_t v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
v___x_1954_ = lean_unbox(v_a_1953_);
lean_dec(v_a_1953_);
if (v___x_1954_ == 0)
{
v___y_1898_ = v___x_1952_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1955_; 
lean_dec_ref_known(v___x_1952_, 1);
v___x_1955_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1764_, v___y_1728_);
v___y_1898_ = v___x_1955_;
goto v___jp_1897_;
}
}
else
{
v___y_1898_ = v___x_1952_;
goto v___jp_1897_;
}
v___jp_1765_:
{
if (lean_obj_tag(v___y_1781_) == 0)
{
lean_object* v_a_1782_; uint8_t v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___y_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___y_1781_, 1);
v___x_1783_ = lean_unbox(v_a_1782_);
lean_dec(v_a_1782_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
else
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1772_, v___y_1767_, v___y_1776_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; uint8_t v___x_1787_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = lean_unbox(v_a_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1759_, v_v_1760_, v___y_1778_, v___y_1776_, v___y_1775_, v___y_1777_, v___y_1768_, v___y_1779_, v___y_1769_, v___y_1773_, v___y_1771_, v___y_1766_, v___y_1770_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1760_, v_u_1759_, v___y_1778_, v___y_1776_, v___y_1775_, v___y_1777_, v___y_1768_, v___y_1779_, v___y_1769_, v___y_1773_, v___y_1771_, v___y_1766_, v___y_1770_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
lean_inc(v_a_1764_);
lean_inc(v_a_1762_);
v___x_1792_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1762_, v_a_1764_, v_a_1789_, v_a_1791_, v___y_1778_, v___y_1776_, v___y_1775_, v___y_1777_, v___y_1768_, v___y_1779_, v___y_1769_, v___y_1773_, v___y_1771_, v___y_1766_, v___y_1770_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
lean_inc(v___y_1770_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1773_);
lean_inc(v_a_1762_);
v___x_1794_ = lean_infer_type(v_a_1762_, v___y_1773_, v___y_1771_, v___y_1766_, v___y_1770_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = l_Lean_Int_mkType;
v___x_1797_ = lean_expr_eqv(v_a_1795_, v___x_1796_);
lean_dec(v_a_1795_);
if (v___x_1797_ == 0)
{
lean_dec(v_a_1793_);
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1767_);
lean_inc_ref(v___y_1772_);
v___x_1800_ = l_Lean_mkApp7(v___x_1799_, v___y_1772_, v___y_1767_, v_a_1762_, v_a_1764_, v___y_1774_, v___y_1780_, v_a_1793_);
v___x_1801_ = lean_unbox(v_a_1786_);
lean_dec(v_a_1786_);
v___x_1802_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1772_, v___y_1767_, v___x_1800_, v___x_1801_, v___y_1776_, v___y_1777_, v___y_1773_, v___y_1771_, v___y_1766_, v___y_1770_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_dec_ref_known(v___x_1802_, 1);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
else
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1793_);
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1804_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1794_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1794_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1812_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1792_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1792_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1789_);
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1820_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1790_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1790_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1828_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1788_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1788_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_dec(v_a_1786_);
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1837_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1785_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1785_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___y_1780_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1845_ = lean_ctor_get(v___y_1781_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___y_1781_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___y_1781_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___y_1781_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
v___jp_1853_:
{
lean_object* v___x_1865_; 
v___x_1865_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1762_, v___y_1855_, v___y_1863_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref_known(v___x_1865_, 1);
if (lean_obj_tag(v_a_1866_) == 1)
{
lean_object* v_val_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; 
v_val_1867_ = lean_ctor_get(v_a_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v_a_1866_, 1);
v_fst_1868_ = lean_ctor_get(v_val_1867_, 0);
lean_inc(v_fst_1868_);
v_snd_1869_ = lean_ctor_get(v_val_1867_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_val_1867_);
v___x_1870_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1764_, v___y_1855_, v___y_1863_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
if (lean_obj_tag(v_a_1871_) == 1)
{
lean_object* v_val_1872_; lean_object* v_fst_1873_; lean_object* v_snd_1874_; lean_object* v___x_1875_; 
v_val_1872_ = lean_ctor_get(v_a_1871_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_a_1871_, 1);
v_fst_1873_ = lean_ctor_get(v_val_1872_, 0);
lean_inc(v_fst_1873_);
v_snd_1874_ = lean_ctor_get(v_val_1872_, 1);
lean_inc(v_snd_1874_);
lean_dec(v_val_1872_);
v___x_1875_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1868_, v___y_1855_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; uint8_t v___x_1877_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
v___x_1877_ = lean_unbox(v_a_1876_);
lean_dec(v_a_1876_);
if (v___x_1877_ == 0)
{
v___y_1766_ = v___y_1863_;
v___y_1767_ = v_fst_1873_;
v___y_1768_ = v___y_1858_;
v___y_1769_ = v___y_1860_;
v___y_1770_ = v___y_1864_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v_fst_1868_;
v___y_1773_ = v___y_1861_;
v___y_1774_ = v_snd_1869_;
v___y_1775_ = v___y_1856_;
v___y_1776_ = v___y_1855_;
v___y_1777_ = v___y_1857_;
v___y_1778_ = v___y_1854_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v_snd_1874_;
v___y_1781_ = v___x_1875_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1878_; 
lean_dec_ref_known(v___x_1875_, 1);
v___x_1878_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1873_, v___y_1855_);
v___y_1766_ = v___y_1863_;
v___y_1767_ = v_fst_1873_;
v___y_1768_ = v___y_1858_;
v___y_1769_ = v___y_1860_;
v___y_1770_ = v___y_1864_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v_fst_1868_;
v___y_1773_ = v___y_1861_;
v___y_1774_ = v_snd_1869_;
v___y_1775_ = v___y_1856_;
v___y_1776_ = v___y_1855_;
v___y_1777_ = v___y_1857_;
v___y_1778_ = v___y_1854_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v_snd_1874_;
v___y_1781_ = v___x_1878_;
goto v___jp_1765_;
}
}
else
{
v___y_1766_ = v___y_1863_;
v___y_1767_ = v_fst_1873_;
v___y_1768_ = v___y_1858_;
v___y_1769_ = v___y_1860_;
v___y_1770_ = v___y_1864_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v_fst_1868_;
v___y_1773_ = v___y_1861_;
v___y_1774_ = v_snd_1869_;
v___y_1775_ = v___y_1856_;
v___y_1776_ = v___y_1855_;
v___y_1777_ = v___y_1857_;
v___y_1778_ = v___y_1854_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v_snd_1874_;
v___y_1781_ = v___x_1875_;
goto v___jp_1765_;
}
}
else
{
lean_dec(v_a_1871_);
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_snd_1869_);
lean_dec(v_fst_1868_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1880_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1870_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1870_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_dec(v_a_1866_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_as_x27_1725_ = v_tail_1741_;
v_b_1726_ = v___x_1742_;
goto _start;
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1889_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1865_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1865_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
v___jp_1897_:
{
if (lean_obj_tag(v___y_1898_) == 0)
{
lean_object* v_a_1899_; uint8_t v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___y_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref_known(v___y_1898_, 1);
v___x_1900_ = lean_unbox(v_a_1899_);
lean_dec(v_a_1899_);
if (v___x_1900_ == 0)
{
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
goto v___jp_1853_;
}
else
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1762_, v_a_1764_, v___y_1728_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; uint8_t v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = lean_unbox(v_a_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1759_, v_v_1760_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1760_, v_u_1759_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
lean_inc(v_a_1764_);
lean_inc(v_a_1762_);
v___x_1908_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1762_, v_a_1764_, v_a_1905_, v_a_1907_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1910_ = lean_unbox(v_a_1902_);
lean_dec(v_a_1902_);
lean_inc(v_a_1764_);
lean_inc(v_a_1762_);
v___x_1911_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1762_, v_a_1764_, v_a_1909_, v___x_1910_, v___y_1728_, v___y_1730_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_dec_ref_known(v___x_1911_, 1);
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
goto v___jp_1853_;
}
else
{
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
return v___x_1911_;
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1902_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1912_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1908_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1908_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1905_);
lean_dec(v_a_1902_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1920_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1906_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1906_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1902_);
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1928_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1904_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1904_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_dec(v_a_1902_);
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
goto v___jp_1853_;
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1936_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1901_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1901_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
v_a_1944_ = lean_ctor_get(v___y_1898_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___y_1898_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___y_1898_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___y_1898_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1762_);
v_a_1956_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1763_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1763_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
v_a_1964_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1761_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1761_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1972_, lean_object* v_b_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1972_, v_b_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v_as_x27_1972_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_Meta_Grind_Order_getStruct(v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___f_2002_; lean_object* v___x_2003_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___f_2002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_2003_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_2002_, v_a_1988_, v_a_1989_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_propagate_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref_known(v___x_2003_, 1);
v_propagate_2004_ = lean_ctor_get(v_a_2001_, 21);
lean_inc(v_propagate_2004_);
lean_dec(v_a_2001_);
v___x_2005_ = lean_box(0);
v___x_2006_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_2004_, v___x_2005_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_propagate_2004_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v___x_2006_, 0);
lean_dec(v_unused_2014_);
v___x_2008_ = v___x_2006_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_dec(v___x_2006_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2005_);
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2005_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
return v___x_2006_;
}
}
else
{
lean_dec(v_a_2001_);
return v___x_2003_;
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
v_a_2015_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2000_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2000_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec(v_a_2024_);
lean_dec(v_a_2023_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2036_, lean_object* v_as_x27_2037_, lean_object* v_b_2038_, lean_object* v_a_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2037_, v_b_2038_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2053_, lean_object* v_as_x27_2054_, lean_object* v_b_2055_, lean_object* v_a_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2053_, v_as_x27_2054_, v_b_2055_, v_a_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec(v_as_x27_2054_);
lean_dec(v_as_2053_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2071_, v_a_2075_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v_termMapInv_2080_; lean_object* v___x_2081_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v_termMapInv_2080_ = lean_ctor_get(v_a_2079_, 4);
lean_inc_ref(v_termMapInv_2080_);
lean_dec(v_a_2079_);
v___x_2081_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2080_, v_e_2070_);
lean_dec_ref(v_termMapInv_2080_);
if (lean_obj_tag(v___x_2081_) == 1)
{
lean_object* v_val_2082_; lean_object* v_fst_2083_; lean_object* v___x_2084_; 
lean_dec_ref(v_e_2070_);
v_val_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_val_2082_);
lean_dec_ref_known(v___x_2081_, 1);
v_fst_2083_ = lean_ctor_get(v_val_2082_, 0);
lean_inc(v_fst_2083_);
lean_dec(v_val_2082_);
v___x_2084_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2083_, v_a_2071_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v___x_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
v___x_2086_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2086_ == 0)
{
lean_dec(v_fst_2083_);
return v___x_2084_;
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref_known(v___x_2084_, 1);
v___x_2087_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2083_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
return v___x_2087_;
}
}
else
{
lean_dec(v_fst_2083_);
return v___x_2084_;
}
}
else
{
lean_object* v___x_2088_; 
lean_dec(v___x_2081_);
v___x_2088_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; uint8_t v___x_2090_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
v___x_2090_ = lean_unbox(v_a_2089_);
lean_dec(v_a_2089_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v_e_2070_);
return v___x_2088_;
}
else
{
lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_2088_, 1);
v___x_2091_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_);
return v___x_2091_;
}
}
else
{
lean_dec_ref(v_e_2070_);
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v_e_2070_);
v_a_2092_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2078_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2078_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2109_, v_a_2111_, v_a_2115_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec(v_a_2124_);
return v_res_2136_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2145_ = l_Lean_Name_append(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2150_, lean_object* v_v_2151_, lean_object* v_k_2152_, lean_object* v_c_2153_, lean_object* v_e_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v___x_2167_; 
lean_inc_ref(v_e_2154_);
v___x_2167_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2154_, v_a_2156_, v_a_2160_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2266_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2266_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2266_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_unbox(v_a_2168_);
lean_dec(v_a_2168_);
if (v___x_2172_ == 0)
{
lean_object* v_options_2173_; lean_object* v_inheritedTraceOptions_2174_; uint8_t v_hasTrace_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; 
v_options_2173_ = lean_ctor_get(v_a_2164_, 2);
v_inheritedTraceOptions_2174_ = lean_ctor_get(v_a_2164_, 13);
v_hasTrace_2175_ = lean_ctor_get_uint8(v_options_2173_, sizeof(void*)*1);
v___x_2176_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2153_);
v___x_2177_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2152_, v___x_2176_);
if (v_hasTrace_2175_ == 0)
{
v___y_2179_ = v_a_2155_;
v___y_2180_ = v_a_2156_;
v___y_2181_ = v_a_2157_;
v___y_2182_ = v_a_2158_;
v___y_2183_ = v_a_2159_;
v___y_2184_ = v_a_2160_;
v___y_2185_ = v_a_2161_;
v___y_2186_ = v_a_2162_;
v___y_2187_ = v_a_2163_;
v___y_2188_ = v_a_2164_;
v___y_2189_ = v_a_2165_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2174_, v_options_2173_, v___x_2197_);
if (v___x_2198_ == 0)
{
v___y_2179_ = v_a_2155_;
v___y_2180_ = v_a_2156_;
v___y_2181_ = v_a_2157_;
v___y_2182_ = v_a_2158_;
v___y_2183_ = v_a_2159_;
v___y_2184_ = v_a_2160_;
v___y_2185_ = v_a_2161_;
v___y_2186_ = v_a_2162_;
v___y_2187_ = v_a_2163_;
v___y_2188_ = v_a_2164_;
v___y_2189_ = v_a_2165_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2150_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2151_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2153_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_k_2205_; uint8_t v_strict_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___y_2223_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v_k_2205_ = lean_ctor_get(v_k_2152_, 0);
v_strict_2206_ = lean_ctor_get_uint8(v_k_2152_, sizeof(void*)*1);
v___x_2207_ = l_Lean_MessageData_ofExpr(v_a_2200_);
v___x_2208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2207_);
lean_ctor_set(v___x_2218_, 1, v___x_2208_);
v___x_2219_ = l_Lean_MessageData_ofExpr(v_a_2202_);
v___x_2220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2218_);
lean_ctor_set(v___x_2220_, 1, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2208_);
if (v_strict_2206_ == 0)
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Int_repr(v_k_2205_);
v___y_2223_ = v___x_2234_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = l_Int_repr(v_k_2205_);
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2237_ = lean_string_append(v___x_2235_, v___x_2236_);
v___y_2223_ = v___x_2237_;
goto v___jp_2222_;
}
v___jp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___y_2211_);
v___x_2213_ = l_Lean_MessageData_ofFormat(v___x_2212_);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___y_2210_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2208_);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_a_2204_);
v___x_2217_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2196_, v___x_2216_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v___y_2179_ = v_a_2155_;
v___y_2180_ = v_a_2156_;
v___y_2181_ = v_a_2157_;
v___y_2182_ = v_a_2158_;
v___y_2183_ = v_a_2159_;
v___y_2184_ = v_a_2160_;
v___y_2185_ = v_a_2161_;
v___y_2186_ = v_a_2162_;
v___y_2187_ = v_a_2163_;
v___y_2188_ = v_a_2164_;
v___y_2189_ = v_a_2165_;
goto v___jp_2178_;
}
else
{
lean_dec_ref(v___x_2176_);
lean_del_object(v___x_2170_);
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
return v___x_2217_;
}
}
v___jp_2222_:
{
lean_object* v_k_2224_; uint8_t v_strict_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_k_2224_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_k_2224_);
v_strict_2225_ = lean_ctor_get_uint8(v___x_2176_, sizeof(void*)*1);
v___x_2226_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___y_2223_);
v___x_2227_ = l_Lean_MessageData_ofFormat(v___x_2226_);
v___x_2228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2221_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
lean_ctor_set(v___x_2229_, 1, v___x_2208_);
if (v_strict_2225_ == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Int_repr(v_k_2224_);
lean_dec(v_k_2224_);
v___y_2210_ = v___x_2229_;
v___y_2211_ = v___x_2230_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = l_Int_repr(v_k_2224_);
lean_dec(v_k_2224_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
v___y_2210_ = v___x_2229_;
v___y_2211_ = v___x_2233_;
goto v___jp_2209_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_a_2202_);
lean_dec(v_a_2200_);
lean_dec_ref(v___x_2176_);
lean_del_object(v___x_2170_);
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v_a_2238_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2203_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2203_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v_a_2200_);
lean_dec_ref(v___x_2176_);
lean_del_object(v___x_2170_);
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v_a_2246_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2201_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2201_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec_ref(v___x_2176_);
lean_del_object(v___x_2170_);
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v_a_2254_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2199_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2199_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
v___jp_2178_:
{
if (v___x_2177_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v___x_2176_);
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v___x_2190_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2190_);
v___x_2192_ = v___x_2170_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_del_object(v___x_2170_);
v___x_2194_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2194_, 0, v_c_2153_);
lean_ctor_set(v___x_2194_, 1, v_e_2154_);
lean_ctor_set(v___x_2194_, 2, v_u_2150_);
lean_ctor_set(v___x_2194_, 3, v_v_2151_);
lean_ctor_set(v___x_2194_, 4, v_k_2152_);
lean_ctor_set(v___x_2194_, 5, v___x_2176_);
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2194_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
return v___x_2195_;
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v___x_2262_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2262_);
v___x_2264_ = v___x_2170_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_e_2154_);
lean_dec_ref(v_c_2153_);
lean_dec_ref(v_k_2152_);
lean_dec(v_v_2151_);
lean_dec(v_u_2150_);
v_a_2267_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2167_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2167_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2275_ = _args[0];
lean_object* v_v_2276_ = _args[1];
lean_object* v_k_2277_ = _args[2];
lean_object* v_c_2278_ = _args[3];
lean_object* v_e_2279_ = _args[4];
lean_object* v_a_2280_ = _args[5];
lean_object* v_a_2281_ = _args[6];
lean_object* v_a_2282_ = _args[7];
lean_object* v_a_2283_ = _args[8];
lean_object* v_a_2284_ = _args[9];
lean_object* v_a_2285_ = _args[10];
lean_object* v_a_2286_ = _args[11];
lean_object* v_a_2287_ = _args[12];
lean_object* v_a_2288_ = _args[13];
lean_object* v_a_2289_ = _args[14];
lean_object* v_a_2290_ = _args[15];
lean_object* v_a_2291_ = _args[16];
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2275_, v_v_2276_, v_k_2277_, v_c_2278_, v_e_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec(v_a_2280_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2294_, v_a_2298_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v_termMapInv_2303_; lean_object* v___x_2304_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
v_termMapInv_2303_ = lean_ctor_get(v_a_2302_, 4);
lean_inc_ref(v_termMapInv_2303_);
lean_dec(v_a_2302_);
v___x_2304_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2303_, v_e_2293_);
lean_dec_ref(v_termMapInv_2303_);
if (lean_obj_tag(v___x_2304_) == 1)
{
lean_object* v_val_2305_; lean_object* v_fst_2306_; lean_object* v___x_2307_; 
lean_dec_ref(v_e_2293_);
v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_val_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_fst_2306_ = lean_ctor_get(v_val_2305_, 0);
lean_inc(v_fst_2306_);
lean_dec(v_val_2305_);
v___x_2307_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2306_, v_a_2294_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; uint8_t v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
v___x_2309_ = lean_unbox(v_a_2308_);
lean_dec(v_a_2308_);
if (v___x_2309_ == 0)
{
lean_dec(v_fst_2306_);
return v___x_2307_;
}
else
{
lean_object* v___x_2310_; 
lean_dec_ref_known(v___x_2307_, 1);
v___x_2310_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2306_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2310_;
}
}
else
{
lean_dec(v_fst_2306_);
return v___x_2307_;
}
}
else
{
lean_object* v___x_2311_; 
lean_dec(v___x_2304_);
v___x_2311_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2293_, v_a_2294_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; uint8_t v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
v___x_2313_ = lean_unbox(v_a_2312_);
lean_dec(v_a_2312_);
if (v___x_2313_ == 0)
{
lean_dec_ref(v_e_2293_);
return v___x_2311_;
}
else
{
lean_object* v___x_2314_; 
lean_dec_ref_known(v___x_2311_, 1);
v___x_2314_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
return v___x_2314_;
}
}
else
{
lean_dec_ref(v_e_2293_);
return v___x_2311_;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v_e_2293_);
v_a_2315_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2301_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2301_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2332_, v_a_2334_, v_a_2338_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec(v_a_2347_);
return v_res_2359_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2368_ = l_Lean_Name_append(v___x_2367_, v___x_2366_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2371_ = l_Lean_stringToMessageData(v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2372_, lean_object* v_v_2373_, lean_object* v_k_2374_, lean_object* v_c_2375_, lean_object* v_e_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2389_; 
lean_inc_ref(v_e_2376_);
v___x_2389_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2376_, v_a_2378_, v_a_2382_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2490_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2392_ = v___x_2389_;
v_isShared_2393_ = v_isSharedCheck_2490_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2389_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2490_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_unbox(v_a_2390_);
lean_dec(v_a_2390_);
if (v___x_2394_ == 0)
{
lean_object* v_options_2395_; lean_object* v_inheritedTraceOptions_2396_; uint8_t v_hasTrace_2397_; lean_object* v___x_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; 
v_options_2395_ = lean_ctor_get(v_a_2386_, 2);
v_inheritedTraceOptions_2396_ = lean_ctor_get(v_a_2386_, 13);
v_hasTrace_2397_ = lean_ctor_get_uint8(v_options_2395_, sizeof(void*)*1);
v___x_2398_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2375_);
if (v_hasTrace_2397_ == 0)
{
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
v___y_2405_ = v_a_2382_;
v___y_2406_ = v_a_2383_;
v___y_2407_ = v_a_2384_;
v___y_2408_ = v_a_2385_;
v___y_2409_ = v_a_2386_;
v___y_2410_ = v_a_2387_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2396_, v_options_2395_, v___x_2420_);
if (v___x_2421_ == 0)
{
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
v___y_2405_ = v_a_2382_;
v___y_2406_ = v_a_2383_;
v___y_2407_ = v_a_2384_;
v___y_2408_ = v_a_2385_;
v___y_2409_ = v_a_2386_;
v___y_2410_ = v_a_2387_;
goto v___jp_2399_;
}
else
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2372_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_a_2423_);
lean_dec_ref_known(v___x_2422_, 1);
v___x_2424_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2373_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2375_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___y_2429_; lean_object* v___y_2430_; lean_object* v_k_2438_; uint8_t v_strict_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___y_2447_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v_k_2438_ = lean_ctor_get(v_k_2374_, 0);
v_strict_2439_ = lean_ctor_get_uint8(v_k_2374_, sizeof(void*)*1);
v___x_2440_ = l_Lean_MessageData_ofExpr(v_a_2423_);
v___x_2441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2440_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
v___x_2443_ = l_Lean_MessageData_ofExpr(v_a_2425_);
v___x_2444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2442_);
lean_ctor_set(v___x_2444_, 1, v___x_2443_);
v___x_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v___x_2441_);
if (v_strict_2439_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Int_repr(v_k_2438_);
v___y_2447_ = v___x_2458_;
goto v___jp_2446_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = l_Int_repr(v_k_2438_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2461_ = lean_string_append(v___x_2459_, v___x_2460_);
v___y_2447_ = v___x_2461_;
goto v___jp_2446_;
}
v___jp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2430_);
v___x_2432_ = l_Lean_MessageData_ofFormat(v___x_2431_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___y_2429_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_a_2427_);
v___x_2437_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2419_, v___x_2436_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_dec_ref_known(v___x_2437_, 1);
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
v___y_2405_ = v_a_2382_;
v___y_2406_ = v_a_2383_;
v___y_2407_ = v_a_2384_;
v___y_2408_ = v_a_2385_;
v___y_2409_ = v_a_2386_;
v___y_2410_ = v_a_2387_;
goto v___jp_2399_;
}
else
{
lean_dec_ref(v___x_2398_);
lean_del_object(v___x_2392_);
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
return v___x_2437_;
}
}
v___jp_2446_:
{
lean_object* v_k_2448_; uint8_t v_strict_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_k_2448_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_k_2448_);
v_strict_2449_ = lean_ctor_get_uint8(v___x_2398_, sizeof(void*)*1);
v___x_2450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2450_, 0, v___y_2447_);
v___x_2451_ = l_Lean_MessageData_ofFormat(v___x_2450_);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2445_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2453_, 0, v___x_2452_);
lean_ctor_set(v___x_2453_, 1, v___x_2441_);
if (v_strict_2449_ == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Int_repr(v_k_2448_);
lean_dec(v_k_2448_);
v___y_2429_ = v___x_2453_;
v___y_2430_ = v___x_2454_;
goto v___jp_2428_;
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = l_Int_repr(v_k_2448_);
lean_dec(v_k_2448_);
v___x_2456_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2457_ = lean_string_append(v___x_2455_, v___x_2456_);
v___y_2429_ = v___x_2453_;
v___y_2430_ = v___x_2457_;
goto v___jp_2428_;
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
lean_dec(v_a_2425_);
lean_dec(v_a_2423_);
lean_dec_ref(v___x_2398_);
lean_del_object(v___x_2392_);
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v_a_2462_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2426_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2426_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_a_2423_);
lean_dec_ref(v___x_2398_);
lean_del_object(v___x_2392_);
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v_a_2470_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2424_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2424_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v___x_2398_);
lean_del_object(v___x_2392_);
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v_a_2478_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2422_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2422_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
v___jp_2399_:
{
lean_object* v___x_2411_; uint8_t v___x_2412_; 
lean_inc_ref(v___x_2398_);
v___x_2411_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2374_, v___x_2398_);
v___x_2412_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2411_);
lean_dec_ref(v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_dec_ref(v___x_2398_);
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v___x_2413_ = lean_box(0);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2413_);
v___x_2415_ = v___x_2392_;
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
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_del_object(v___x_2392_);
v___x_2417_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2417_, 0, v_c_2375_);
lean_ctor_set(v___x_2417_, 1, v_e_2376_);
lean_ctor_set(v___x_2417_, 2, v_u_2372_);
lean_ctor_set(v___x_2417_, 3, v_v_2373_);
lean_ctor_set(v___x_2417_, 4, v_k_2374_);
lean_ctor_set(v___x_2417_, 5, v___x_2398_);
v___x_2418_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2417_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2418_;
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v___x_2486_ = lean_box(0);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 0, v___x_2486_);
v___x_2488_ = v___x_2392_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
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
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_e_2376_);
lean_dec_ref(v_c_2375_);
lean_dec_ref(v_k_2374_);
lean_dec(v_v_2373_);
lean_dec(v_u_2372_);
v_a_2491_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2389_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2389_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2499_ = _args[0];
lean_object* v_v_2500_ = _args[1];
lean_object* v_k_2501_ = _args[2];
lean_object* v_c_2502_ = _args[3];
lean_object* v_e_2503_ = _args[4];
lean_object* v_a_2504_ = _args[5];
lean_object* v_a_2505_ = _args[6];
lean_object* v_a_2506_ = _args[7];
lean_object* v_a_2507_ = _args[8];
lean_object* v_a_2508_ = _args[9];
lean_object* v_a_2509_ = _args[10];
lean_object* v_a_2510_ = _args[11];
lean_object* v_a_2511_ = _args[12];
lean_object* v_a_2512_ = _args[13];
lean_object* v_a_2513_ = _args[14];
lean_object* v_a_2514_ = _args[15];
lean_object* v_a_2515_ = _args[16];
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2499_, v_v_2500_, v_k_2501_, v_c_2502_, v_e_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec(v_a_2504_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2517_, lean_object* v_x_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_fst_2531_; lean_object* v_snd_2532_; lean_object* v___x_2533_; 
v_fst_2531_ = lean_ctor_get(v_x_2518_, 0);
lean_inc(v_fst_2531_);
v_snd_2532_ = lean_ctor_get(v_x_2518_, 1);
lean_inc(v_snd_2532_);
lean_dec_ref(v_x_2518_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc_ref(v___y_2524_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc(v___y_2519_);
v___x_2533_ = lean_apply_14(v_f_2517_, v_fst_2531_, v_snd_2532_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, lean_box(0));
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2534_, lean_object* v_x_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2534_, v_x_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec(v___y_2536_);
return v_res_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___f_2553_; 
v___x_2552_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2553_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2553_, 0, v___x_2552_);
return v___f_2553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2554_; lean_object* v___f_2555_; 
v___f_2554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2555_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2555_, 0, v___f_2554_);
lean_closure_set(v___f_2555_, 1, v___f_2554_);
return v___f_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2556_, lean_object* v_v_2557_, lean_object* v_f_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
lean_object* v___x_2571_; lean_object* v_toApplicative_2572_; lean_object* v_toFunctor_2573_; lean_object* v_toSeq_2574_; lean_object* v_toSeqLeft_2575_; lean_object* v_toSeqRight_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___f_2579_; lean_object* v___f_2580_; lean_object* v___x_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v_toApplicative_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2649_; 
v___x_2571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2572_ = lean_ctor_get(v___x_2571_, 0);
v_toFunctor_2573_ = lean_ctor_get(v_toApplicative_2572_, 0);
v_toSeq_2574_ = lean_ctor_get(v_toApplicative_2572_, 2);
v_toSeqLeft_2575_ = lean_ctor_get(v_toApplicative_2572_, 3);
v_toSeqRight_2576_ = lean_ctor_get(v_toApplicative_2572_, 4);
v___f_2577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2573_, 2);
v___f_2579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2579_, 0, v_toFunctor_2573_);
v___f_2580_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2580_, 0, v_toFunctor_2573_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___f_2579_);
lean_ctor_set(v___x_2581_, 1, v___f_2580_);
lean_inc(v_toSeqRight_2576_);
v___f_2582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2582_, 0, v_toSeqRight_2576_);
lean_inc(v_toSeqLeft_2575_);
v___f_2583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2583_, 0, v_toSeqLeft_2575_);
lean_inc(v_toSeq_2574_);
v___f_2584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2584_, 0, v_toSeq_2574_);
v___x_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2581_);
lean_ctor_set(v___x_2585_, 1, v___f_2577_);
lean_ctor_set(v___x_2585_, 2, v___f_2584_);
lean_ctor_set(v___x_2585_, 3, v___f_2583_);
lean_ctor_set(v___x_2585_, 4, v___f_2582_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___f_2578_);
v___x_2587_ = l_StateRefT_x27_instMonad___redArg(v___x_2586_);
v_toApplicative_2588_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2649_ == 0)
{
lean_object* v_unused_2650_; 
v_unused_2650_ = lean_ctor_get(v___x_2587_, 1);
lean_dec(v_unused_2650_);
v___x_2590_ = v___x_2587_;
v_isShared_2591_ = v_isSharedCheck_2649_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_toApplicative_2588_);
lean_dec(v___x_2587_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2649_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v_toFunctor_2592_; lean_object* v_toSeq_2593_; lean_object* v_toSeqLeft_2594_; lean_object* v_toSeqRight_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2647_; 
v_toFunctor_2592_ = lean_ctor_get(v_toApplicative_2588_, 0);
v_toSeq_2593_ = lean_ctor_get(v_toApplicative_2588_, 2);
v_toSeqLeft_2594_ = lean_ctor_get(v_toApplicative_2588_, 3);
v_toSeqRight_2595_ = lean_ctor_get(v_toApplicative_2588_, 4);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_toApplicative_2588_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_toApplicative_2588_, 1);
lean_dec(v_unused_2648_);
v___x_2597_ = v_toApplicative_2588_;
v_isShared_2598_ = v_isSharedCheck_2647_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_toSeqRight_2595_);
lean_inc(v_toSeqLeft_2594_);
lean_inc(v_toSeq_2593_);
lean_inc(v_toFunctor_2592_);
lean_dec(v_toApplicative_2588_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2647_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___x_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___x_2608_; 
v___f_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2592_);
v___f_2601_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2601_, 0, v_toFunctor_2592_);
v___f_2602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2602_, 0, v_toFunctor_2592_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___f_2601_);
lean_ctor_set(v___x_2603_, 1, v___f_2602_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toSeqRight_2595_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toSeqLeft_2594_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toSeq_2593_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 4, v___f_2604_);
lean_ctor_set(v___x_2597_, 3, v___f_2605_);
lean_ctor_set(v___x_2597_, 2, v___f_2606_);
lean_ctor_set(v___x_2597_, 1, v___f_2599_);
lean_ctor_set(v___x_2597_, 0, v___x_2603_);
v___x_2608_ = v___x_2597_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___f_2599_);
lean_ctor_set(v_reuseFailAlloc_2646_, 2, v___f_2606_);
lean_ctor_set(v_reuseFailAlloc_2646_, 3, v___f_2605_);
lean_ctor_set(v_reuseFailAlloc_2646_, 4, v___f_2604_);
v___x_2608_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2591_ == 0)
{
lean_ctor_set(v___x_2590_, 1, v___f_2600_);
lean_ctor_set(v___x_2590_, 0, v___x_2608_);
v___x_2610_ = v___x_2590_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2608_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v___f_2600_);
v___x_2610_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; 
v___x_2611_ = l_StateRefT_x27_instMonad___redArg(v___x_2610_);
v___x_2612_ = l_ReaderT_instMonad___redArg(v___x_2611_);
v___x_2613_ = l_StateRefT_x27_instMonad___redArg(v___x_2612_);
v___x_2614_ = l_ReaderT_instMonad___redArg(v___x_2613_);
v___x_2615_ = l_ReaderT_instMonad___redArg(v___x_2614_);
v___x_2616_ = l_StateRefT_x27_instMonad___redArg(v___x_2615_);
v___x_2617_ = l_ReaderT_instMonad___redArg(v___x_2616_);
v___f_2618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2619_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2636_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2622_ = v___x_2619_;
v_isShared_2623_ = v_isSharedCheck_2636_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2636_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___f_2624_; lean_object* v_cnstrsOf_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___f_2624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2625_ = lean_ctor_get(v_a_2620_, 17);
lean_inc_ref(v_cnstrsOf_2625_);
lean_dec(v_a_2620_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v_u_2556_);
lean_ctor_set(v___x_2626_, 1, v_v_2557_);
v___x_2627_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2624_, v___f_2618_, v_cnstrsOf_2625_, v___x_2626_);
lean_dec_ref(v_cnstrsOf_2625_);
if (lean_obj_tag(v___x_2627_) == 1)
{
lean_object* v_val_2628_; lean_object* v___f_2629_; lean_object* v___x_1457__overap_2630_; lean_object* v___x_2631_; 
lean_del_object(v___x_2622_);
v_val_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_val_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___f_2629_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2629_, 0, v_f_2558_);
v___x_1457__overap_2630_ = l_List_forM___redArg(v___x_2617_, v_val_2628_, v___f_2629_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc_ref(v_a_2564_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc(v_a_2560_);
lean_inc(v_a_2559_);
v___x_2631_ = lean_apply_12(v___x_1457__overap_2630_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, lean_box(0));
return v___x_2631_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_dec(v___x_2627_);
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_f_2558_);
v___x_2632_ = lean_box(0);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2632_);
v___x_2634_ = v___x_2622_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec_ref(v___x_2617_);
lean_dec_ref(v_f_2558_);
lean_dec(v_v_2557_);
lean_dec(v_u_2556_);
v_a_2637_ = lean_ctor_get(v___x_2619_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2619_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2619_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2651_, lean_object* v_v_2652_, lean_object* v_f_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2651_, v_v_2652_, v_f_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec(v_a_2654_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2668_, v_a_2669_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2694_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2694_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2694_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_termMapInv_2676_; lean_object* v___x_2677_; 
v_termMapInv_2676_ = lean_ctor_get(v_a_2672_, 4);
lean_inc_ref(v_termMapInv_2676_);
lean_dec(v_a_2672_);
v___x_2677_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2676_, v_e_2667_);
lean_dec_ref(v_termMapInv_2676_);
if (lean_obj_tag(v___x_2677_) == 1)
{
lean_object* v_val_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2689_; 
v_val_2678_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2680_ = v___x_2677_;
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_val_2678_);
lean_dec(v___x_2677_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_fst_2682_; lean_object* v___x_2684_; 
v_fst_2682_ = lean_ctor_get(v_val_2678_, 0);
lean_inc(v_fst_2682_);
lean_dec(v_val_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v_fst_2682_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_fst_2682_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2684_);
v___x_2686_ = v___x_2674_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
lean_dec(v___x_2677_);
v___x_2690_ = lean_box(0);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v___x_2690_);
v___x_2692_ = v___x_2674_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2671_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2671_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2703_, v_a_2704_, v_a_2705_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_e_2703_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2708_, v_a_2709_, v_a_2717_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec_ref(v_a_2726_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_e_2721_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2734_, lean_object* v_v_2735_, lean_object* v_k_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___x_2792_; 
v___x_2792_ = lean_nat_dec_eq(v_u_2734_, v_v_2735_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2931_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2931_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2931_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_unbox(v_a_2794_);
lean_dec(v_a_2794_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2799_ = lean_box(0);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2799_);
v___x_2801_ = v___x_2796_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
else
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2736_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2804_ = lean_box(0);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2804_);
v___x_2806_ = v___x_2796_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
lean_object* v___x_2808_; 
lean_del_object(v___x_2796_);
v___x_2808_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_2735_, v_u_2734_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2922_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2922_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2922_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
if (lean_obj_tag(v_a_2809_) == 1)
{
lean_object* v_val_2813_; uint8_t v___x_2814_; 
v_val_2813_ = lean_ctor_get(v_a_2809_, 0);
lean_inc(v_val_2813_);
lean_dec_ref_known(v_a_2809_, 1);
v___x_2814_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2813_);
lean_dec(v_val_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2815_ = lean_box(0);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2815_);
v___x_2817_ = v___x_2811_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
else
{
lean_object* v___x_2819_; 
lean_del_object(v___x_2811_);
v___x_2819_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2734_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; lean_object* v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___x_2821_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2735_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___y_2824_; lean_object* v___x_2898_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2898_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2820_, v_a_2738_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; uint8_t v___x_2900_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
v___x_2900_ = lean_unbox(v_a_2899_);
lean_dec(v_a_2899_);
if (v___x_2900_ == 0)
{
v___y_2824_ = v___x_2898_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2901_; 
lean_dec_ref_known(v___x_2898_, 1);
v___x_2901_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2822_, v_a_2738_);
v___y_2824_ = v___x_2901_;
goto v___jp_2823_;
}
}
else
{
v___y_2824_ = v___x_2898_;
goto v___jp_2823_;
}
v___jp_2823_:
{
if (lean_obj_tag(v___y_2824_) == 0)
{
lean_object* v_a_2825_; uint8_t v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___y_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___y_2824_, 1);
v___x_2826_ = lean_unbox(v_a_2825_);
lean_dec(v_a_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2820_, v_a_2738_, v_a_2746_);
lean_dec(v_a_2820_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2860_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2860_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2860_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2860_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
if (lean_obj_tag(v_a_2828_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2833_; 
lean_del_object(v___x_2830_);
v_val_2832_ = lean_ctor_get(v_a_2828_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_2828_, 1);
v___x_2833_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2822_, v_a_2738_, v_a_2746_);
lean_dec(v_a_2822_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2847_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2847_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2847_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
if (lean_obj_tag(v_a_2834_) == 1)
{
lean_object* v_val_2838_; lean_object* v___x_2839_; 
lean_del_object(v___x_2836_);
v_val_2838_ = lean_ctor_get(v_a_2834_, 0);
lean_inc(v_val_2838_);
lean_dec_ref_known(v_a_2834_, 1);
v___x_2839_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2832_, v_a_2738_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; uint8_t v___x_2841_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
v___x_2841_ = lean_unbox(v_a_2840_);
lean_dec(v_a_2840_);
if (v___x_2841_ == 0)
{
v___y_2750_ = v_val_2838_;
v___y_2751_ = v_val_2832_;
v___y_2752_ = v___x_2839_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2842_; 
lean_dec_ref_known(v___x_2839_, 1);
v___x_2842_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2838_, v_a_2738_);
v___y_2750_ = v_val_2838_;
v___y_2751_ = v_val_2832_;
v___y_2752_ = v___x_2842_;
goto v___jp_2749_;
}
}
else
{
v___y_2750_ = v_val_2838_;
v___y_2751_ = v_val_2832_;
v___y_2752_ = v___x_2839_;
goto v___jp_2749_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
lean_dec(v_a_2834_);
lean_dec(v_val_2832_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2843_ = lean_box(0);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2843_);
v___x_2845_ = v___x_2836_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_val_2832_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2848_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2833_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2833_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v___x_2856_; lean_object* v___x_2858_; 
lean_dec(v_a_2828_);
lean_dec(v_a_2822_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2856_ = lean_box(0);
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 0, v___x_2856_);
v___x_2858_ = v___x_2830_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v___x_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_a_2822_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2861_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2827_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2827_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v___x_2869_; 
v___x_2869_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2820_, v_a_2822_, v_a_2738_);
lean_dec(v_a_2822_);
lean_dec(v_a_2820_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2881_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
uint8_t v___x_2874_; 
v___x_2874_ = lean_unbox(v_a_2870_);
lean_dec(v_a_2870_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_del_object(v___x_2872_);
v___x_2875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2875_, 0, v_u_2734_);
lean_ctor_set(v___x_2875_, 1, v_v_2735_);
v___x_2876_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2875_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2876_;
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2879_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2877_ = lean_box(0);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2877_);
v___x_2879_ = v___x_2872_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2882_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2869_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2869_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_a_2822_);
lean_dec(v_a_2820_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2890_ = lean_ctor_get(v___y_2824_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___y_2824_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___y_2824_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___y_2824_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2820_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2902_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2821_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2821_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2910_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2819_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2819_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2920_; 
lean_dec(v_a_2809_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2918_ = lean_box(0);
if (v_isShared_2812_ == 0)
{
lean_ctor_set(v___x_2811_, 0, v___x_2918_);
v___x_2920_ = v___x_2811_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2923_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2808_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2808_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2932_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2793_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2793_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
v___jp_2749_:
{
if (lean_obj_tag(v___y_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2783_; 
v_a_2753_ = lean_ctor_get(v___y_2752_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___y_2752_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2755_ = v___y_2752_;
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___y_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2783_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
uint8_t v___x_2757_; 
v___x_2757_ = lean_unbox(v_a_2753_);
lean_dec(v_a_2753_);
if (v___x_2757_ == 0)
{
lean_object* v___x_2758_; lean_object* v___x_2760_; 
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2758_ = lean_box(0);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2758_);
v___x_2760_ = v___x_2755_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2758_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
else
{
lean_object* v___x_2762_; 
lean_del_object(v___x_2755_);
v___x_2762_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2751_, v___y_2750_, v_a_2738_);
lean_dec_ref(v___y_2750_);
lean_dec_ref(v___y_2751_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2774_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2765_ = v___x_2762_;
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_a_2763_);
lean_dec(v___x_2762_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2774_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
uint8_t v___x_2767_; 
v___x_2767_ = lean_unbox(v_a_2763_);
lean_dec(v_a_2763_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_del_object(v___x_2765_);
v___x_2768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_u_2734_);
lean_ctor_set(v___x_2768_, 1, v_v_2735_);
v___x_2769_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2768_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v___x_2770_ = lean_box(0);
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 0, v___x_2770_);
v___x_2772_ = v___x_2765_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2775_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2762_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2762_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v_v_2735_);
lean_dec(v_u_2734_);
v_a_2784_ = lean_ctor_get(v___y_2752_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___y_2752_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___y_2752_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___y_2752_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2942_, lean_object* v_v_2943_, lean_object* v_k_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2942_, v_v_2943_, v_k_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_k_2944_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2958_, lean_object* v_vals_2959_, lean_object* v_i_2960_, lean_object* v_k_2961_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_array_get_size(v_keys_2958_);
v___x_2967_ = lean_nat_dec_lt(v_i_2960_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; 
lean_dec(v_i_2960_);
v___x_2968_ = lean_box(0);
return v___x_2968_;
}
else
{
lean_object* v_fst_2969_; lean_object* v_snd_2970_; lean_object* v_k_x27_2971_; lean_object* v_fst_2972_; lean_object* v_snd_2973_; uint8_t v___x_2974_; 
v_fst_2969_ = lean_ctor_get(v_k_2961_, 0);
v_snd_2970_ = lean_ctor_get(v_k_2961_, 1);
v_k_x27_2971_ = lean_array_fget_borrowed(v_keys_2958_, v_i_2960_);
v_fst_2972_ = lean_ctor_get(v_k_x27_2971_, 0);
v_snd_2973_ = lean_ctor_get(v_k_x27_2971_, 1);
v___x_2974_ = lean_nat_dec_eq(v_fst_2969_, v_fst_2972_);
if (v___x_2974_ == 0)
{
goto v___jp_2962_;
}
else
{
uint8_t v___x_2975_; 
v___x_2975_ = lean_nat_dec_eq(v_snd_2970_, v_snd_2973_);
if (v___x_2975_ == 0)
{
goto v___jp_2962_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_array_fget_borrowed(v_vals_2959_, v_i_2960_);
lean_dec(v_i_2960_);
lean_inc(v___x_2976_);
v___x_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
return v___x_2977_;
}
}
}
v___jp_2962_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = lean_nat_add(v_i_2960_, v___x_2963_);
lean_dec(v_i_2960_);
v_i_2960_ = v___x_2964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2978_, lean_object* v_vals_2979_, lean_object* v_i_2980_, lean_object* v_k_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2978_, v_vals_2979_, v_i_2980_, v_k_2981_);
lean_dec_ref(v_k_2981_);
lean_dec_ref(v_vals_2979_);
lean_dec_ref(v_keys_2978_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2983_, size_t v_x_2984_, lean_object* v_x_2985_){
_start:
{
if (lean_obj_tag(v_x_2983_) == 0)
{
lean_object* v_es_2986_; lean_object* v___x_2987_; size_t v___x_2988_; size_t v___x_2989_; lean_object* v_j_2990_; lean_object* v___x_2991_; 
v_es_2986_ = lean_ctor_get(v_x_2983_, 0);
v___x_2987_ = lean_box(2);
v___x_2988_ = ((size_t)31ULL);
v___x_2989_ = lean_usize_land(v_x_2984_, v___x_2988_);
v_j_2990_ = lean_usize_to_nat(v___x_2989_);
v___x_2991_ = lean_array_get_borrowed(v___x_2987_, v_es_2986_, v_j_2990_);
lean_dec(v_j_2990_);
switch(lean_obj_tag(v___x_2991_))
{
case 0:
{
lean_object* v_key_2992_; lean_object* v_val_2993_; lean_object* v_fst_2994_; lean_object* v_snd_2995_; lean_object* v_fst_2996_; lean_object* v_snd_2997_; uint8_t v___x_2998_; 
v_key_2992_ = lean_ctor_get(v___x_2991_, 0);
v_val_2993_ = lean_ctor_get(v___x_2991_, 1);
v_fst_2994_ = lean_ctor_get(v_x_2985_, 0);
v_snd_2995_ = lean_ctor_get(v_x_2985_, 1);
v_fst_2996_ = lean_ctor_get(v_key_2992_, 0);
v_snd_2997_ = lean_ctor_get(v_key_2992_, 1);
v___x_2998_ = lean_nat_dec_eq(v_fst_2994_, v_fst_2996_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; 
v___x_2999_ = lean_box(0);
return v___x_2999_;
}
else
{
uint8_t v___x_3000_; 
v___x_3000_ = lean_nat_dec_eq(v_snd_2995_, v_snd_2997_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; 
v___x_3001_ = lean_box(0);
return v___x_3001_;
}
else
{
lean_object* v___x_3002_; 
lean_inc(v_val_2993_);
v___x_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_val_2993_);
return v___x_3002_;
}
}
}
case 1:
{
lean_object* v_node_3003_; size_t v___x_3004_; size_t v___x_3005_; 
v_node_3003_ = lean_ctor_get(v___x_2991_, 0);
v___x_3004_ = ((size_t)5ULL);
v___x_3005_ = lean_usize_shift_right(v_x_2984_, v___x_3004_);
v_x_2983_ = v_node_3003_;
v_x_2984_ = v___x_3005_;
goto _start;
}
default: 
{
lean_object* v___x_3007_; 
v___x_3007_ = lean_box(0);
return v___x_3007_;
}
}
}
else
{
lean_object* v_ks_3008_; lean_object* v_vs_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_ks_3008_ = lean_ctor_get(v_x_2983_, 0);
v_vs_3009_ = lean_ctor_get(v_x_2983_, 1);
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_3008_, v_vs_3009_, v___x_3010_, v_x_2985_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_3012_, lean_object* v_x_3013_, lean_object* v_x_3014_){
_start:
{
size_t v_x_3987__boxed_3015_; lean_object* v_res_3016_; 
v_x_3987__boxed_3015_ = lean_unbox_usize(v_x_3013_);
lean_dec(v_x_3013_);
v_res_3016_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3012_, v_x_3987__boxed_3015_, v_x_3014_);
lean_dec_ref(v_x_3014_);
lean_dec_ref(v_x_3012_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
lean_object* v_fst_3019_; lean_object* v_snd_3020_; uint64_t v___x_3021_; uint64_t v___x_3022_; uint64_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
v_fst_3019_ = lean_ctor_get(v_x_3018_, 0);
v_snd_3020_ = lean_ctor_get(v_x_3018_, 1);
v___x_3021_ = lean_uint64_of_nat(v_fst_3019_);
v___x_3022_ = lean_uint64_of_nat(v_snd_3020_);
v___x_3023_ = lean_uint64_mix_hash(v___x_3021_, v___x_3022_);
v___x_3024_ = lean_uint64_to_usize(v___x_3023_);
v___x_3025_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3017_, v___x_3024_, v_x_3018_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3026_, v_x_3027_);
lean_dec_ref(v_x_3027_);
lean_dec_ref(v_x_3026_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3029_, lean_object* v_v_3030_, lean_object* v_k_3031_, lean_object* v_as_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
if (lean_obj_tag(v_as_3032_) == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
lean_dec_ref(v_k_3031_);
lean_dec(v_v_3030_);
lean_dec(v_u_3029_);
v___x_3045_ = lean_box(0);
v___x_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
return v___x_3046_;
}
else
{
lean_object* v_head_3047_; lean_object* v_tail_3048_; lean_object* v_fst_3049_; lean_object* v_snd_3050_; lean_object* v___x_3051_; 
v_head_3047_ = lean_ctor_get(v_as_3032_, 0);
lean_inc(v_head_3047_);
v_tail_3048_ = lean_ctor_get(v_as_3032_, 1);
lean_inc(v_tail_3048_);
lean_dec_ref_known(v_as_3032_, 2);
v_fst_3049_ = lean_ctor_get(v_head_3047_, 0);
lean_inc(v_fst_3049_);
v_snd_3050_ = lean_ctor_get(v_head_3047_, 1);
lean_inc(v_snd_3050_);
lean_dec(v_head_3047_);
lean_inc_ref(v_k_3031_);
lean_inc(v_v_3030_);
lean_inc(v_u_3029_);
v___x_3051_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3029_, v_v_3030_, v_k_3031_, v_fst_3049_, v_snd_3050_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_dec_ref_known(v___x_3051_, 1);
v_as_3032_ = v_tail_3048_;
goto _start;
}
else
{
lean_dec(v_tail_3048_);
lean_dec_ref(v_k_3031_);
lean_dec(v_v_3030_);
lean_dec(v_u_3029_);
return v___x_3051_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3053_, lean_object* v_v_3054_, lean_object* v_k_3055_, lean_object* v_as_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3053_, v_v_3054_, v_k_3055_, v_as_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec(v___y_3057_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3070_, lean_object* v_v_3071_, lean_object* v_k_3072_, lean_object* v_as_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
if (lean_obj_tag(v_as_3073_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec_ref(v_k_3072_);
lean_dec(v_v_3071_);
lean_dec(v_u_3070_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
else
{
lean_object* v_head_3088_; lean_object* v_tail_3089_; lean_object* v_fst_3090_; lean_object* v_snd_3091_; lean_object* v___x_3092_; 
v_head_3088_ = lean_ctor_get(v_as_3073_, 0);
lean_inc(v_head_3088_);
v_tail_3089_ = lean_ctor_get(v_as_3073_, 1);
lean_inc(v_tail_3089_);
lean_dec_ref_known(v_as_3073_, 2);
v_fst_3090_ = lean_ctor_get(v_head_3088_, 0);
lean_inc(v_fst_3090_);
v_snd_3091_ = lean_ctor_get(v_head_3088_, 1);
lean_inc(v_snd_3091_);
lean_dec(v_head_3088_);
lean_inc_ref(v_k_3072_);
lean_inc(v_v_3071_);
lean_inc(v_u_3070_);
v___x_3092_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3070_, v_v_3071_, v_k_3072_, v_fst_3090_, v_snd_3091_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_dec_ref_known(v___x_3092_, 1);
v_as_3073_ = v_tail_3089_;
goto _start;
}
else
{
lean_dec(v_tail_3089_);
lean_dec_ref(v_k_3072_);
lean_dec(v_v_3071_);
lean_dec(v_u_3070_);
return v___x_3092_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3094_, lean_object* v_v_3095_, lean_object* v_k_3096_, lean_object* v_as_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3094_, v_v_3095_, v_k_3096_, v_as_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec(v___y_3098_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3111_, lean_object* v_v_3112_, lean_object* v_k_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v_cnstrsOf_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v_cnstrsOf_3146_ = lean_ctor_get(v_a_3145_, 17);
lean_inc_ref(v_cnstrsOf_3146_);
lean_dec(v_a_3145_);
lean_inc(v_v_3112_);
lean_inc(v_u_3111_);
v___x_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3147_, 0, v_u_3111_);
lean_ctor_set(v___x_3147_, 1, v_v_3112_);
v___x_3148_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3146_, v___x_3147_);
lean_dec_ref_known(v___x_3147_, 2);
lean_dec_ref(v_cnstrsOf_3146_);
if (lean_obj_tag(v___x_3148_) == 1)
{
lean_object* v_val_3149_; lean_object* v___x_3150_; 
v_val_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_val_3149_);
lean_dec_ref_known(v___x_3148_, 1);
lean_inc_ref(v_k_3113_);
lean_inc(v_v_3112_);
lean_inc(v_u_3111_);
v___x_3150_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3111_, v_v_3112_, v_k_3113_, v_val_3149_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_dec_ref_known(v___x_3150_, 1);
goto v___jp_3126_;
}
else
{
lean_dec_ref(v_k_3113_);
lean_dec(v_v_3112_);
lean_dec(v_u_3111_);
return v___x_3150_;
}
}
else
{
lean_dec(v___x_3148_);
goto v___jp_3126_;
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v_k_3113_);
lean_dec(v_v_3112_);
lean_dec(v_u_3111_);
v_a_3151_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3144_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3144_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
v___jp_3126_:
{
lean_object* v___x_3127_; 
v___x_3127_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v_cnstrsOf_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v_cnstrsOf_3129_ = lean_ctor_get(v_a_3128_, 17);
lean_inc_ref(v_cnstrsOf_3129_);
lean_dec(v_a_3128_);
lean_inc(v_u_3111_);
lean_inc(v_v_3112_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v_v_3112_);
lean_ctor_set(v___x_3130_, 1, v_u_3111_);
v___x_3131_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3129_, v___x_3130_);
lean_dec_ref_known(v___x_3130_, 2);
lean_dec_ref(v_cnstrsOf_3129_);
if (lean_obj_tag(v___x_3131_) == 1)
{
lean_object* v_val_3132_; lean_object* v___x_3133_; 
v_val_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v___x_3131_, 1);
lean_inc_ref(v_k_3113_);
lean_inc(v_v_3112_);
lean_inc(v_u_3111_);
v___x_3133_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3111_, v_v_3112_, v_k_3113_, v_val_3132_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v___x_3134_; 
lean_dec_ref_known(v___x_3133_, 1);
v___x_3134_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3111_, v_v_3112_, v_k_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec_ref(v_k_3113_);
return v___x_3134_;
}
else
{
lean_dec_ref(v_k_3113_);
lean_dec(v_v_3112_);
lean_dec(v_u_3111_);
return v___x_3133_;
}
}
else
{
lean_object* v___x_3135_; 
lean_dec(v___x_3131_);
v___x_3135_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3111_, v_v_3112_, v_k_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_);
lean_dec_ref(v_k_3113_);
return v___x_3135_;
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v_k_3113_);
lean_dec(v_v_3112_);
lean_dec(v_u_3111_);
v_a_3136_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3127_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3127_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3159_, lean_object* v_v_3160_, lean_object* v_k_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3159_, v_v_3160_, v_k_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec(v_a_3162_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3175_, lean_object* v_x_3176_, lean_object* v_x_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3176_, v_x_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3179_, v_x_3180_, v_x_3181_);
lean_dec_ref(v_x_3181_);
lean_dec_ref(v_x_3180_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3183_, lean_object* v_x_3184_, size_t v_x_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3184_, v_x_3185_, v_x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3188_, lean_object* v_x_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
size_t v_x_4251__boxed_3192_; lean_object* v_res_3193_; 
v_x_4251__boxed_3192_ = lean_unbox_usize(v_x_3190_);
lean_dec(v_x_3190_);
v_res_3193_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3188_, v_x_3189_, v_x_4251__boxed_3192_, v_x_3191_);
lean_dec_ref(v_x_3191_);
lean_dec_ref(v_x_3189_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3194_, lean_object* v_keys_3195_, lean_object* v_vals_3196_, lean_object* v_heq_3197_, lean_object* v_i_3198_, lean_object* v_k_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3195_, v_vals_3196_, v_i_3198_, v_k_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3201_, lean_object* v_keys_3202_, lean_object* v_vals_3203_, lean_object* v_heq_3204_, lean_object* v_i_3205_, lean_object* v_k_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3201_, v_keys_3202_, v_vals_3203_, v_heq_3204_, v_i_3205_, v_k_3206_);
lean_dec_ref(v_k_3206_);
lean_dec_ref(v_vals_3203_);
lean_dec_ref(v_keys_3202_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3208_, lean_object* v_v_3209_, lean_object* v_k_3210_, lean_object* v_w_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3208_, v_v_3209_, v_k_3210_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3247_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3227_ = v___x_3224_;
v_isShared_3228_ = v_isSharedCheck_3247_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3247_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
uint8_t v___x_3229_; 
v___x_3229_ = lean_unbox(v_a_3225_);
lean_dec(v_a_3225_);
if (v___x_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_dec_ref(v_k_3210_);
lean_dec(v_v_3209_);
lean_dec(v_u_3208_);
v___x_3230_ = lean_box(0);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3230_);
v___x_3232_ = v___x_3227_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
else
{
lean_object* v___x_3234_; 
lean_del_object(v___x_3227_);
lean_inc_ref(v_k_3210_);
lean_inc(v_v_3209_);
lean_inc(v_u_3208_);
v___x_3234_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3208_, v_v_3209_, v_k_3210_, v_a_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v___x_3235_; 
lean_dec_ref_known(v___x_3234_, 1);
v___x_3235_ = l_Lean_Meta_Grind_Order_getProof(v_w_3211_, v_v_3209_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
lean_inc(v_v_3209_);
lean_inc(v_u_3208_);
v___x_3237_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3208_, v_v_3209_, v_a_3236_, v_a_3212_, v_a_3213_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3238_; 
lean_dec_ref_known(v___x_3237_, 1);
v___x_3238_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3208_, v_v_3209_, v_k_3210_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_);
return v___x_3238_;
}
else
{
lean_dec_ref(v_k_3210_);
lean_dec(v_v_3209_);
lean_dec(v_u_3208_);
return v___x_3237_;
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v_k_3210_);
lean_dec(v_v_3209_);
lean_dec(v_u_3208_);
v_a_3239_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3235_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3235_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_dec_ref(v_k_3210_);
lean_dec(v_v_3209_);
lean_dec(v_u_3208_);
return v___x_3234_;
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v_k_3210_);
lean_dec(v_v_3209_);
lean_dec(v_u_3208_);
v_a_3248_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3224_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3224_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3256_, lean_object* v_v_3257_, lean_object* v_k_3258_, lean_object* v_w_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3256_, v_v_3257_, v_k_3258_, v_w_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec(v_w_3259_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3273_, lean_object* v_i_3274_, lean_object* v_v_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
if (lean_obj_tag(v_x_3276_) == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_i_3274_);
v___x_3289_ = lean_box(0);
v___x_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
return v___x_3290_;
}
else
{
lean_object* v_key_3291_; lean_object* v_value_3292_; lean_object* v_tail_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v_key_3291_ = lean_ctor_get(v_x_3276_, 0);
lean_inc(v_key_3291_);
v_value_3292_ = lean_ctor_get(v_x_3276_, 1);
lean_inc(v_value_3292_);
v_tail_3293_ = lean_ctor_get(v_x_3276_, 2);
lean_inc(v_tail_3293_);
lean_dec_ref_known(v_x_3276_, 3);
v___x_3294_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3273_, v_value_3292_);
lean_inc(v_i_3274_);
v___x_3295_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3274_, v_key_3291_, v___x_3294_, v_v_3275_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_dec_ref_known(v___x_3295_, 1);
v_x_3276_ = v_tail_3293_;
goto _start;
}
else
{
lean_dec(v_tail_3293_);
lean_dec(v_i_3274_);
return v___x_3295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3297_, lean_object* v_i_3298_, lean_object* v_v_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3297_, v_i_3298_, v_v_3299_, v_x_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v_v_3299_);
lean_dec_ref(v___x_3297_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3314_, lean_object* v_v_3315_, lean_object* v_u_3316_, lean_object* v_x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
if (lean_obj_tag(v_x_3317_) == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_dec(v_v_3315_);
lean_dec_ref(v_k_3314_);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
return v___x_3331_;
}
else
{
lean_object* v_key_3332_; lean_object* v_value_3333_; lean_object* v_tail_3334_; lean_object* v___y_3336_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_key_3332_ = lean_ctor_get(v_x_3317_, 0);
lean_inc_n(v_key_3332_, 2);
v_value_3333_ = lean_ctor_get(v_x_3317_, 1);
lean_inc(v_value_3333_);
v_tail_3334_ = lean_ctor_get(v_x_3317_, 2);
lean_inc(v_tail_3334_);
lean_dec_ref_known(v_x_3317_, 3);
lean_inc_ref(v_k_3314_);
v___x_3338_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3333_, v_k_3314_);
lean_dec(v_value_3333_);
lean_inc_ref(v___x_3338_);
lean_inc(v_v_3315_);
v___x_3339_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3332_, v_v_3315_, v___x_3338_, v_u_3316_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref_known(v___x_3339_, 1);
v___x_3340_ = l_Lean_Meta_Grind_Order_getStruct(v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v_targets_3342_; lean_object* v_size_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v_targets_3342_ = lean_ctor_get(v_a_3341_, 19);
lean_inc_ref(v_targets_3342_);
lean_dec(v_a_3341_);
v_size_3343_ = lean_ctor_get(v_targets_3342_, 2);
v___x_3344_ = lean_box(0);
v___x_3345_ = lean_nat_dec_lt(v_v_3315_, v_size_3343_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec_ref(v_targets_3342_);
v___x_3346_ = l_outOfBounds___redArg(v___x_3344_);
v___x_3347_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3338_, v_key_3332_, v_v_3315_, v___x_3346_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec_ref(v___x_3338_);
v___y_3336_ = v___x_3347_;
goto v___jp_3335_;
}
else
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3344_, v_targets_3342_, v_v_3315_);
lean_dec_ref(v_targets_3342_);
v___x_3349_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3338_, v_key_3332_, v_v_3315_, v___x_3348_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec_ref(v___x_3338_);
v___y_3336_ = v___x_3349_;
goto v___jp_3335_;
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec_ref(v___x_3338_);
lean_dec(v_tail_3334_);
lean_dec(v_key_3332_);
lean_dec(v_v_3315_);
lean_dec_ref(v_k_3314_);
v_a_3350_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3340_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3340_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_dec_ref(v___x_3338_);
lean_dec(v_key_3332_);
v___y_3336_ = v___x_3339_;
goto v___jp_3335_;
}
v___jp_3335_:
{
if (lean_obj_tag(v___y_3336_) == 0)
{
lean_dec_ref_known(v___y_3336_, 1);
v_x_3317_ = v_tail_3334_;
goto _start;
}
else
{
lean_dec(v_tail_3334_);
lean_dec(v_v_3315_);
lean_dec_ref(v_k_3314_);
return v___y_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3358_, lean_object* v_v_3359_, lean_object* v_u_3360_, lean_object* v_x_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3358_, v_v_3359_, v_u_3360_, v_x_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec(v___y_3362_);
lean_dec(v_u_3360_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3375_, lean_object* v_v_3376_, lean_object* v_k_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
lean_object* v___y_3391_; lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v_targets_3412_; lean_object* v_size_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref_known(v___x_3410_, 1);
v_targets_3412_ = lean_ctor_get(v_a_3411_, 19);
lean_inc_ref(v_targets_3412_);
lean_dec(v_a_3411_);
v_size_3413_ = lean_ctor_get(v_targets_3412_, 2);
v___x_3414_ = lean_box(0);
v___x_3415_ = lean_nat_dec_lt(v_v_3376_, v_size_3413_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v_targets_3412_);
v___x_3416_ = l_outOfBounds___redArg(v___x_3414_);
lean_inc(v_u_3375_);
v___x_3417_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3377_, v_u_3375_, v_v_3376_, v___x_3416_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3391_ = v___x_3417_;
goto v___jp_3390_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3414_, v_targets_3412_, v_v_3376_);
lean_dec_ref(v_targets_3412_);
lean_inc(v_u_3375_);
v___x_3419_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3377_, v_u_3375_, v_v_3376_, v___x_3418_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
v___y_3391_ = v___x_3419_;
goto v___jp_3390_;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_k_3377_);
lean_dec(v_v_3376_);
lean_dec(v_u_3375_);
v_a_3420_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3410_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3410_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
v___jp_3390_:
{
if (lean_obj_tag(v___y_3391_) == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref_known(v___y_3391_, 1);
v___x_3392_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v_sources_3394_; lean_object* v_size_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v_sources_3394_ = lean_ctor_get(v_a_3393_, 18);
lean_inc_ref(v_sources_3394_);
lean_dec(v_a_3393_);
v_size_3395_ = lean_ctor_get(v_sources_3394_, 2);
v___x_3396_ = lean_box(0);
v___x_3397_ = lean_nat_dec_lt(v_u_3375_, v_size_3395_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v_sources_3394_);
v___x_3398_ = l_outOfBounds___redArg(v___x_3396_);
v___x_3399_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3377_, v_v_3376_, v_u_3375_, v___x_3398_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_u_3375_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3396_, v_sources_3394_, v_u_3375_);
lean_dec_ref(v_sources_3394_);
v___x_3401_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3377_, v_v_3376_, v_u_3375_, v___x_3400_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_);
lean_dec(v_u_3375_);
return v___x_3401_;
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_k_3377_);
lean_dec(v_v_3376_);
lean_dec(v_u_3375_);
v_a_3402_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3392_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3392_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_dec_ref(v_k_3377_);
lean_dec(v_v_3376_);
lean_dec(v_u_3375_);
return v___y_3391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3428_, lean_object* v_v_3429_, lean_object* v_k_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3428_, v_v_3429_, v_k_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec(v_a_3431_);
return v_res_3443_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3452_ = l_Lean_Name_append(v___x_3451_, v___x_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3453_, lean_object* v_v_3454_, lean_object* v_k_3455_, lean_object* v_h_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3458_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3621_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3621_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3621_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_unbox(v_a_3545_);
lean_dec(v_a_3545_);
if (v___x_3549_ == 0)
{
uint8_t v___x_3550_; 
lean_del_object(v___x_3547_);
v___x_3550_ = lean_nat_dec_eq(v_u_3453_, v_v_3454_);
if (v___x_3550_ == 0)
{
lean_object* v_options_3551_; uint8_t v_hasTrace_3552_; 
v_options_3551_ = lean_ctor_get(v_a_3466_, 2);
v_hasTrace_3552_ = lean_ctor_get_uint8(v_options_3551_, sizeof(void*)*1);
if (v_hasTrace_3552_ == 0)
{
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
goto v___jp_3506_;
}
else
{
lean_object* v_inheritedTraceOptions_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_inheritedTraceOptions_3553_ = lean_ctor_get(v_a_3466_, 13);
v___x_3554_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3555_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3553_, v_options_3551_, v___x_3555_);
if (v___x_3556_ == 0)
{
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
goto v___jp_3506_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3453_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Meta_Grind_Order_getExpr(v_v_3454_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v_k_3561_; uint8_t v_strict_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___y_3570_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v_k_3561_ = lean_ctor_get(v_k_3455_, 0);
v_strict_3562_ = lean_ctor_get_uint8(v_k_3455_, sizeof(void*)*1);
v___x_3563_ = l_Lean_MessageData_ofExpr(v_a_3558_);
v___x_3564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3563_);
lean_ctor_set(v___x_3565_, 1, v___x_3564_);
v___x_3566_ = l_Lean_MessageData_ofExpr(v_a_3560_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3565_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v___x_3564_);
if (v_strict_3562_ == 0)
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Int_repr(v_k_3561_);
v___y_3570_ = v___x_3575_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v___x_3576_ = l_Int_repr(v_k_3561_);
v___x_3577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3578_ = lean_string_append(v___x_3576_, v___x_3577_);
v___y_3570_ = v___x_3578_;
goto v___jp_3569_;
}
v___jp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___y_3570_);
v___x_3572_ = l_Lean_MessageData_ofFormat(v___x_3571_);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3568_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3554_, v___x_3573_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_dec_ref_known(v___x_3574_, 1);
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
goto v___jp_3506_;
}
else
{
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
return v___x_3574_;
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec(v_a_3558_);
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v_a_3579_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3559_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3559_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v_a_3587_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3557_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3557_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
}
}
}
else
{
uint8_t v___x_3595_; 
lean_dec(v_v_3454_);
v___x_3595_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3455_);
if (v___x_3595_ == 0)
{
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_u_3453_);
goto v___jp_3541_;
}
else
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3453_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec(v_u_3453_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3597_, v_k_3455_, v_h_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
lean_dec_ref(v_k_3455_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = l_Lean_Meta_Grind_closeGoal(v_a_3599_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_dec_ref_known(v___x_3600_, 1);
goto v___jp_3541_;
}
else
{
return v___x_3600_;
}
}
else
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3608_; 
v_a_3601_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3603_ = v___x_3598_;
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3598_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3608_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3606_; 
if (v_isShared_3604_ == 0)
{
v___x_3606_ = v___x_3603_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
v_a_3609_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3596_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3596_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v___x_3617_ = lean_box(0);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3617_);
v___x_3619_ = v___x_3547_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v_a_3622_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3544_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3544_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
v___jp_3469_:
{
lean_object* v___x_3481_; 
v___x_3481_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3453_, v_v_3454_, v_k_3455_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3497_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3497_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3497_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
uint8_t v___x_3486_; 
v___x_3486_ = lean_unbox(v_a_3482_);
lean_dec(v_a_3482_);
if (v___x_3486_ == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v___x_3487_ = lean_box(0);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3487_);
v___x_3489_ = v___x_3484_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
else
{
lean_object* v___x_3491_; 
lean_del_object(v___x_3484_);
lean_inc_ref(v_k_3455_);
lean_inc(v_v_3454_);
lean_inc(v_u_3453_);
v___x_3491_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3453_, v_v_3454_, v_k_3455_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec_ref_known(v___x_3491_, 1);
lean_inc_ref(v_k_3455_);
lean_inc_n(v_u_3453_, 2);
v___x_3492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3492_, 0, v_u_3453_);
lean_ctor_set(v___x_3492_, 1, v_k_3455_);
lean_ctor_set(v___x_3492_, 2, v_h_3456_);
lean_inc(v_v_3454_);
v___x_3493_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3453_, v_v_3454_, v___x_3492_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v___x_3494_; 
lean_dec_ref_known(v___x_3493_, 1);
lean_inc_ref(v_k_3455_);
lean_inc(v_v_3454_);
lean_inc(v_u_3453_);
v___x_3494_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3453_, v_v_3454_, v_k_3455_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v___x_3495_; 
lean_dec_ref_known(v___x_3494_, 1);
v___x_3495_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3453_, v_v_3454_, v_k_3455_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v___x_3496_; 
lean_dec_ref_known(v___x_3495_, 1);
v___x_3496_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
return v___x_3496_;
}
else
{
return v___x_3495_;
}
}
else
{
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
return v___x_3494_;
}
}
else
{
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
return v___x_3493_;
}
}
else
{
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v_a_3498_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3481_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3481_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_3454_, v_u_3453_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
if (lean_obj_tag(v_a_3519_) == 1)
{
lean_object* v_val_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_val_3520_ = lean_ctor_get(v_a_3519_, 0);
lean_inc_n(v_val_3520_, 2);
lean_dec_ref_known(v_a_3519_, 1);
v___x_3521_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3455_, v_val_3520_);
v___x_3522_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3521_);
lean_dec_ref(v___x_3521_);
if (v___x_3522_ == 0)
{
lean_dec(v_val_3520_);
v___y_3470_ = v___y_3507_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3509_;
v___y_3473_ = v___y_3510_;
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
v___y_3476_ = v___y_3513_;
v___y_3477_ = v___y_3514_;
v___y_3478_ = v___y_3515_;
v___y_3479_ = v___y_3516_;
v___y_3480_ = v___y_3517_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3453_, v_v_3454_, v_k_3455_, v_h_3456_, v_val_3520_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v_val_3520_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3531_; 
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3531_ == 0)
{
lean_object* v_unused_3532_; 
v_unused_3532_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3532_);
v___x_3525_ = v___x_3523_;
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v___x_3523_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = lean_box(0);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
else
{
return v___x_3523_;
}
}
}
else
{
lean_dec(v_a_3519_);
v___y_3470_ = v___y_3507_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3509_;
v___y_3473_ = v___y_3510_;
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
v___y_3476_ = v___y_3513_;
v___y_3477_ = v___y_3514_;
v___y_3478_ = v___y_3515_;
v___y_3479_ = v___y_3516_;
v___y_3480_ = v___y_3517_;
goto v___jp_3469_;
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v_h_3456_);
lean_dec_ref(v_k_3455_);
lean_dec(v_v_3454_);
lean_dec(v_u_3453_);
v_a_3533_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3518_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3518_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
v___jp_3541_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_box(0);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3630_, lean_object* v_v_3631_, lean_object* v_k_3632_, lean_object* v_h_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3630_, v_v_3631_, v_k_3632_, v_h_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec(v_a_3634_);
return v_res_3646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3653_ = lean_box(0);
v___x_3654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3655_ = l_Lean_mkConst(v___x_3654_, v___x_3653_);
return v___x_3655_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_cls_3661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3662_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3663_ = l_Lean_Name_append(v___x_3662_, v_cls_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3664_, lean_object* v_e_3665_, lean_object* v_he_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; uint8_t v___y_3695_; lean_object* v_h_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_options_3739_; uint8_t v_hasTrace_3740_; 
v_options_3739_ = lean_ctor_get(v_a_3676_, 2);
v_hasTrace_3740_ = lean_ctor_get_uint8(v_options_3739_, sizeof(void*)*1);
if (v_hasTrace_3740_ == 0)
{
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
goto v___jp_3720_;
}
else
{
lean_object* v_inheritedTraceOptions_3741_; lean_object* v_cls_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; 
v_inheritedTraceOptions_3741_ = lean_ctor_get(v_a_3676_, 13);
v_cls_3742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3743_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3741_, v_options_3739_, v___x_3743_);
if (v___x_3744_ == 0)
{
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3664_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3742_, v_a_3746_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_dec_ref_known(v___x_3747_, 1);
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
goto v___jp_3720_;
}
else
{
lean_dec_ref(v_he_3666_);
lean_dec_ref(v_e_3665_);
lean_dec_ref(v_c_3664_);
return v___x_3747_;
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec_ref(v_he_3666_);
lean_dec_ref(v_e_3665_);
lean_dec_ref(v_c_3664_);
v_a_3748_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3745_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3745_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
v___jp_3679_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3696_, 0, v___y_3692_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*1, v___y_3695_);
v___x_3697_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3681_, v___y_3688_, v___x_3696_, v___y_3690_, v___y_3694_, v___y_3687_, v___y_3691_, v___y_3683_, v___y_3686_, v___y_3685_, v___y_3693_, v___y_3682_, v___y_3689_, v___y_3684_, v___y_3680_);
return v___x_3697_;
}
v___jp_3698_:
{
uint8_t v_kind_3711_; 
v_kind_3711_ = lean_ctor_get_uint8(v_c_3664_, sizeof(void*)*5);
if (v_kind_3711_ == 1)
{
lean_object* v_u_3712_; lean_object* v_v_3713_; lean_object* v_k_3714_; uint8_t v___x_3715_; 
v_u_3712_ = lean_ctor_get(v_c_3664_, 0);
lean_inc(v_u_3712_);
v_v_3713_ = lean_ctor_get(v_c_3664_, 1);
lean_inc(v_v_3713_);
v_k_3714_ = lean_ctor_get(v_c_3664_, 2);
lean_inc(v_k_3714_);
lean_dec_ref(v_c_3664_);
v___x_3715_ = 1;
v___y_3680_ = v___y_3710_;
v___y_3681_ = v_u_3712_;
v___y_3682_ = v___y_3707_;
v___y_3683_ = v___y_3703_;
v___y_3684_ = v___y_3709_;
v___y_3685_ = v___y_3705_;
v___y_3686_ = v___y_3704_;
v___y_3687_ = v___y_3701_;
v___y_3688_ = v_v_3713_;
v___y_3689_ = v___y_3708_;
v___y_3690_ = v_h_3699_;
v___y_3691_ = v___y_3702_;
v___y_3692_ = v_k_3714_;
v___y_3693_ = v___y_3706_;
v___y_3694_ = v___y_3700_;
v___y_3695_ = v___x_3715_;
goto v___jp_3679_;
}
else
{
lean_object* v_u_3716_; lean_object* v_v_3717_; lean_object* v_k_3718_; uint8_t v___x_3719_; 
v_u_3716_ = lean_ctor_get(v_c_3664_, 0);
lean_inc(v_u_3716_);
v_v_3717_ = lean_ctor_get(v_c_3664_, 1);
lean_inc(v_v_3717_);
v_k_3718_ = lean_ctor_get(v_c_3664_, 2);
lean_inc(v_k_3718_);
lean_dec_ref(v_c_3664_);
v___x_3719_ = 0;
v___y_3680_ = v___y_3710_;
v___y_3681_ = v_u_3716_;
v___y_3682_ = v___y_3707_;
v___y_3683_ = v___y_3703_;
v___y_3684_ = v___y_3709_;
v___y_3685_ = v___y_3705_;
v___y_3686_ = v___y_3704_;
v___y_3687_ = v___y_3701_;
v___y_3688_ = v_v_3717_;
v___y_3689_ = v___y_3708_;
v___y_3690_ = v_h_3699_;
v___y_3691_ = v___y_3702_;
v___y_3692_ = v_k_3718_;
v___y_3693_ = v___y_3706_;
v___y_3694_ = v___y_3700_;
v___y_3695_ = v___x_3719_;
goto v___jp_3679_;
}
}
v___jp_3720_:
{
lean_object* v_h_x3f_3732_; 
v_h_x3f_3732_ = lean_ctor_get(v_c_3664_, 4);
if (lean_obj_tag(v_h_x3f_3732_) == 1)
{
lean_object* v_e_3733_; lean_object* v_val_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_e_3733_ = lean_ctor_get(v_c_3664_, 3);
v_val_3734_ = lean_ctor_get(v_h_x3f_3732_, 0);
v___x_3735_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3665_);
v___x_3736_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3665_, v_he_3666_);
lean_inc(v_val_3734_);
lean_inc_ref(v_e_3733_);
v___x_3737_ = l_Lean_mkApp4(v___x_3735_, v_e_3665_, v_e_3733_, v_val_3734_, v___x_3736_);
v_h_3699_ = v___x_3737_;
v___y_3700_ = v___y_3721_;
v___y_3701_ = v___y_3722_;
v___y_3702_ = v___y_3723_;
v___y_3703_ = v___y_3724_;
v___y_3704_ = v___y_3725_;
v___y_3705_ = v___y_3726_;
v___y_3706_ = v___y_3727_;
v___y_3707_ = v___y_3728_;
v___y_3708_ = v___y_3729_;
v___y_3709_ = v___y_3730_;
v___y_3710_ = v___y_3731_;
goto v___jp_3698_;
}
else
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3665_, v_he_3666_);
v_h_3699_ = v___x_3738_;
v___y_3700_ = v___y_3721_;
v___y_3701_ = v___y_3722_;
v___y_3702_ = v___y_3723_;
v___y_3703_ = v___y_3724_;
v___y_3704_ = v___y_3725_;
v___y_3705_ = v___y_3726_;
v___y_3706_ = v___y_3727_;
v___y_3707_ = v___y_3728_;
v___y_3708_ = v___y_3729_;
v___y_3709_ = v___y_3730_;
v___y_3710_ = v___y_3731_;
goto v___jp_3698_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3756_, lean_object* v_e_3757_, lean_object* v_he_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3756_, v_e_3757_, v_he_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec(v_a_3759_);
return v_res_3771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_box(0);
v___x_3779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3780_ = l_Lean_mkConst(v___x_3779_, v___x_3778_);
return v___x_3780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_nat_to_int(v___x_3781_);
return v___x_3782_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = lean_unsigned_to_nat(0u);
v___x_3784_ = lean_nat_to_int(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = lean_unsigned_to_nat(0u);
v___x_3791_ = l_Lean_Level_ofNat(v___x_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3793_);
lean_ctor_set(v___x_3794_, 1, v___x_3792_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3797_ = l_Lean_Expr_const___override(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_box(0);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3803_ = l_Lean_Expr_const___override(v___x_3802_, v___x_3801_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_box(0);
v___x_3809_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3810_ = l_Lean_Expr_const___override(v___x_3809_, v___x_3808_);
return v___x_3810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3847_ = lean_box(0);
v___x_3848_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3849_ = l_Lean_mkConst(v___x_3848_, v___x_3847_);
return v___x_3849_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3852_ = l_Lean_stringToMessageData(v___x_3851_);
return v___x_3852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3853_, lean_object* v_e_3854_, lean_object* v_he_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v_k_x27_3871_; lean_object* v_h_3872_; uint8_t v_strict_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; uint8_t v___y_3929_; lean_object* v___x_3975_; 
v___x_3975_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_4297_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_4297_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_4297_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; uint8_t v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; uint8_t v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v_h_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; uint8_t v___x_4273_; 
v___x_4273_ = lean_unbox(v_a_3976_);
if (v___x_4273_ == 0)
{
lean_object* v___x_4274_; lean_object* v___x_4276_; 
lean_dec(v_a_3976_);
lean_dec_ref(v_he_3855_);
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_c_3853_);
v___x_4274_ = lean_box(0);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_4274_);
v___x_4276_ = v___x_3978_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
else
{
lean_object* v_options_4278_; uint8_t v_hasTrace_4279_; 
lean_del_object(v___x_3978_);
v_options_4278_ = lean_ctor_get(v_a_3865_, 2);
v_hasTrace_4279_ = lean_ctor_get_uint8(v_options_4278_, sizeof(void*)*1);
if (v_hasTrace_4279_ == 0)
{
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
goto v___jp_4254_;
}
else
{
lean_object* v_inheritedTraceOptions_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v_inheritedTraceOptions_4280_ = lean_ctor_get(v_a_3865_, 13);
v___x_4281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4280_, v_options_4278_, v___x_4282_);
if (v___x_4283_ == 0)
{
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
goto v___jp_4254_;
}
else
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3853_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_4284_) == 0)
{
lean_object* v_a_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v_a_4285_ = lean_ctor_get(v___x_4284_, 0);
lean_inc(v_a_4285_);
lean_dec_ref_known(v___x_4284_, 1);
v___x_4286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v_a_4285_);
v___x_4288_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4281_, v___x_4287_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_dec_ref_known(v___x_4288_, 1);
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
goto v___jp_4254_;
}
else
{
lean_dec(v_a_3976_);
lean_dec_ref(v_he_3855_);
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_c_3853_);
return v___x_4288_;
}
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_3976_);
lean_dec_ref(v_he_3855_);
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_c_3853_);
v_a_4289_ = lean_ctor_get(v___x_4284_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4284_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4284_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4284_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
}
}
v___jp_3980_:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_4001_);
v___x_4003_ = l_Lean_mkApp6(v___y_3986_, v___y_3998_, v___y_3982_, v___y_3990_, v___y_4001_, v___x_4002_, v___y_3984_);
if (v___y_3985_ == 0)
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_unbox(v_a_3976_);
lean_dec(v_a_3976_);
v___y_3912_ = v___x_4002_;
v___y_3913_ = v___y_3981_;
v___y_3914_ = v___y_3983_;
v___y_3915_ = v___y_4001_;
v___y_3916_ = v___y_3987_;
v___y_3917_ = v___y_3988_;
v___y_3918_ = v___y_3989_;
v___y_3919_ = v___y_3991_;
v___y_3920_ = v___y_3992_;
v___y_3921_ = v___y_3994_;
v___y_3922_ = v___y_3993_;
v___y_3923_ = v___x_4003_;
v___y_3924_ = v___y_3995_;
v___y_3925_ = v___y_3996_;
v___y_3926_ = v___y_3997_;
v___y_3927_ = v___y_3999_;
v___y_3928_ = v___y_4000_;
v___y_3929_ = v___x_4004_;
goto v___jp_3911_;
}
else
{
uint8_t v___x_4005_; 
lean_dec(v_a_3976_);
v___x_4005_ = 0;
v___y_3912_ = v___x_4002_;
v___y_3913_ = v___y_3981_;
v___y_3914_ = v___y_3983_;
v___y_3915_ = v___y_4001_;
v___y_3916_ = v___y_3987_;
v___y_3917_ = v___y_3988_;
v___y_3918_ = v___y_3989_;
v___y_3919_ = v___y_3991_;
v___y_3920_ = v___y_3992_;
v___y_3921_ = v___y_3994_;
v___y_3922_ = v___y_3993_;
v___y_3923_ = v___x_4003_;
v___y_3924_ = v___y_3995_;
v___y_3925_ = v___y_3996_;
v___y_3926_ = v___y_3997_;
v___y_3927_ = v___y_3999_;
v___y_3928_ = v___y_4000_;
v___y_3929_ = v___x_4005_;
goto v___jp_3911_;
}
}
v___jp_4006_:
{
lean_object* v___x_4027_; uint8_t v___x_4028_; 
v___x_4027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4028_ = lean_int_dec_le(v___x_4027_, v___y_4019_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4031_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4032_ = lean_int_neg(v___y_4019_);
v___x_4033_ = l_Int_toNat(v___x_4032_);
lean_dec(v___x_4032_);
v___x_4034_ = l_Lean_instToExprInt_mkNat(v___x_4033_);
v___x_4035_ = l_Lean_mkApp3(v___x_4029_, v___x_4030_, v___x_4031_, v___x_4034_);
v___y_3981_ = v___y_4007_;
v___y_3982_ = v___y_4008_;
v___y_3983_ = v___y_4009_;
v___y_3984_ = v___y_4010_;
v___y_3985_ = v___y_4011_;
v___y_3986_ = v___y_4012_;
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4014_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4026_;
v___y_3991_ = v___y_4016_;
v___y_3992_ = v___y_4017_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4018_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4021_;
v___y_3997_ = v___y_4023_;
v___y_3998_ = v___y_4022_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___x_4035_;
goto v___jp_3980_;
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = l_Int_toNat(v___y_4019_);
v___x_4037_ = l_Lean_instToExprInt_mkNat(v___x_4036_);
v___y_3981_ = v___y_4007_;
v___y_3982_ = v___y_4008_;
v___y_3983_ = v___y_4009_;
v___y_3984_ = v___y_4010_;
v___y_3985_ = v___y_4011_;
v___y_3986_ = v___y_4012_;
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4014_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4026_;
v___y_3991_ = v___y_4016_;
v___y_3992_ = v___y_4017_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4018_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4021_;
v___y_3997_ = v___y_4023_;
v___y_3998_ = v___y_4022_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___x_4037_;
goto v___jp_3980_;
}
}
v___jp_4038_:
{
lean_object* v___x_4056_; 
lean_inc(v___y_4055_);
v___x_4056_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4055_, v___y_4045_, v___y_4050_, v___y_4049_, v___y_4039_, v___y_4047_, v___y_4048_, v___y_4051_, v___y_4040_, v___y_4053_, v___y_4052_, v___y_4044_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref_known(v___x_4056_, 1);
v___x_4058_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4046_, v___y_4045_, v___y_4050_, v___y_4049_, v___y_4039_, v___y_4047_, v___y_4048_, v___y_4051_, v___y_4040_, v___y_4053_, v___y_4052_, v___y_4044_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4060_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
v___x_4060_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4054_, v___y_4045_, v___y_4050_, v___y_4049_, v___y_4039_, v___y_4047_, v___y_4048_, v___y_4051_, v___y_4040_, v___y_4053_, v___y_4052_, v___y_4044_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = lean_int_neg(v___y_4042_);
v___x_4063_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4064_ = lean_int_dec_le(v___x_4063_, v___y_4042_);
if (v___x_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_dec(v___y_4042_);
v___x_4065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4068_ = l_Int_toNat(v___x_4062_);
v___x_4069_ = l_Lean_instToExprInt_mkNat(v___x_4068_);
v___x_4070_ = l_Lean_mkApp3(v___x_4065_, v___x_4066_, v___x_4067_, v___x_4069_);
v___y_4007_ = v___y_4039_;
v___y_4008_ = v_a_4061_;
v___y_4009_ = v___y_4040_;
v___y_4010_ = v___y_4041_;
v___y_4011_ = v___y_4043_;
v___y_4012_ = v_a_4057_;
v___y_4013_ = v___y_4044_;
v___y_4014_ = v___y_4045_;
v___y_4015_ = v___y_4046_;
v___y_4016_ = v___y_4047_;
v___y_4017_ = v___y_4048_;
v___y_4018_ = v___y_4049_;
v___y_4019_ = v___x_4062_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___y_4051_;
v___y_4022_ = v_a_4059_;
v___y_4023_ = v___y_4052_;
v___y_4024_ = v___y_4053_;
v___y_4025_ = v___y_4054_;
v___y_4026_ = v___x_4070_;
goto v___jp_4006_;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = l_Int_toNat(v___y_4042_);
lean_dec(v___y_4042_);
v___x_4072_ = l_Lean_instToExprInt_mkNat(v___x_4071_);
v___y_4007_ = v___y_4039_;
v___y_4008_ = v_a_4061_;
v___y_4009_ = v___y_4040_;
v___y_4010_ = v___y_4041_;
v___y_4011_ = v___y_4043_;
v___y_4012_ = v_a_4057_;
v___y_4013_ = v___y_4044_;
v___y_4014_ = v___y_4045_;
v___y_4015_ = v___y_4046_;
v___y_4016_ = v___y_4047_;
v___y_4017_ = v___y_4048_;
v___y_4018_ = v___y_4049_;
v___y_4019_ = v___x_4062_;
v___y_4020_ = v___y_4050_;
v___y_4021_ = v___y_4051_;
v___y_4022_ = v_a_4059_;
v___y_4023_ = v___y_4052_;
v___y_4024_ = v___y_4053_;
v___y_4025_ = v___y_4054_;
v___y_4026_ = v___x_4072_;
goto v___jp_4006_;
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_4059_);
lean_dec(v_a_4057_);
lean_dec(v___y_4054_);
lean_dec(v___y_4046_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v_a_3976_);
v_a_4073_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4060_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4060_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4057_);
lean_dec(v___y_4054_);
lean_dec(v___y_4046_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v_a_3976_);
v_a_4081_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4058_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4058_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v___y_4054_);
lean_dec(v___y_4046_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v_a_3976_);
v_a_4089_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4056_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4056_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
v___jp_4097_:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_Meta_Grind_Order_isRing(v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; uint8_t v___x_4112_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4110_, 1);
v___x_4112_ = lean_unbox(v_a_4111_);
if (v___x_4112_ == 0)
{
uint8_t v_kind_4113_; 
v_kind_4113_ = lean_ctor_get_uint8(v_c_3853_, sizeof(void*)*5);
if (v_kind_4113_ == 1)
{
lean_object* v_u_4114_; lean_object* v_v_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
lean_dec(v_a_3976_);
v_u_4114_ = lean_ctor_get(v_c_3853_, 0);
lean_inc(v_u_4114_);
v_v_4115_ = lean_ctor_get(v_c_3853_, 1);
lean_inc(v_v_4115_);
lean_dec_ref(v_c_3853_);
v___x_4116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4117_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4116_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4119_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4117_, 1);
v___x_4119_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4114_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4115_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref_known(v___x_4121_, 1);
v___x_4123_ = l_Lean_mkApp3(v_a_4118_, v_a_4120_, v_a_4122_, v_h_4098_);
v___x_4124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4125_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
v___x_4126_ = lean_unbox(v_a_4111_);
lean_dec(v_a_4111_);
lean_ctor_set_uint8(v___x_4125_, sizeof(void*)*1, v___x_4126_);
v___x_4127_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4115_, v_u_4114_, v___x_4125_, v___x_4123_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4127_;
}
else
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
lean_dec(v_a_4120_);
lean_dec(v_a_4118_);
lean_dec(v_v_4115_);
lean_dec(v_u_4114_);
lean_dec(v_a_4111_);
lean_dec_ref(v_h_4098_);
v_a_4128_ = lean_ctor_get(v___x_4121_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___x_4121_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___x_4121_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec(v_a_4118_);
lean_dec(v_v_4115_);
lean_dec(v_u_4114_);
lean_dec(v_a_4111_);
lean_dec_ref(v_h_4098_);
v_a_4136_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4119_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4119_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec(v_v_4115_);
lean_dec(v_u_4114_);
lean_dec(v_a_4111_);
lean_dec_ref(v_h_4098_);
v_a_4144_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4117_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4117_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v_u_4152_; lean_object* v_v_4153_; lean_object* v___x_4154_; 
lean_dec(v_a_4111_);
v_u_4152_ = lean_ctor_get(v_c_3853_, 0);
lean_inc(v_u_4152_);
v_v_4153_ = lean_ctor_get(v_c_3853_, 1);
lean_inc(v_v_4153_);
lean_dec_ref(v_c_3853_);
v___x_4154_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; uint8_t v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = lean_unbox(v_a_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v_a_3976_);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4158_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4157_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4160_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4152_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4153_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; lean_object* v___x_4168_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = l_Lean_mkApp3(v_a_4159_, v_a_4161_, v_a_4163_, v_h_4098_);
v___x_4165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
v___x_4167_ = lean_unbox(v_a_4155_);
lean_dec(v_a_4155_);
lean_ctor_set_uint8(v___x_4166_, sizeof(void*)*1, v___x_4167_);
v___x_4168_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4153_, v_u_4152_, v___x_4166_, v___x_4164_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4168_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec(v_a_4161_);
lean_dec(v_a_4159_);
lean_dec(v_a_4155_);
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
v_a_4169_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4162_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4162_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
lean_dec(v_a_4159_);
lean_dec(v_a_4155_);
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
v_a_4177_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4160_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4160_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
lean_dec(v_a_4155_);
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
v_a_4185_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___x_4158_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___x_4158_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_dec(v_a_4155_);
v___x_4193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4194_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4193_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4152_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v___x_4198_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4153_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_Lean_mkApp3(v_a_4195_, v_a_4197_, v_a_4199_, v_h_4098_);
v___x_4201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4202_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
v___x_4203_ = lean_unbox(v_a_3976_);
lean_dec(v_a_3976_);
lean_ctor_set_uint8(v___x_4202_, sizeof(void*)*1, v___x_4203_);
v___x_4204_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4153_, v_u_4152_, v___x_4202_, v___x_4200_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4204_;
}
else
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
lean_dec(v_a_4197_);
lean_dec(v_a_4195_);
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
lean_dec(v_a_3976_);
v_a_4205_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4207_ = v___x_4198_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4198_);
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
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec(v_a_4195_);
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
lean_dec(v_a_3976_);
v_a_4213_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4196_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4196_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
lean_dec(v_a_3976_);
v_a_4221_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4194_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4194_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec(v_v_4153_);
lean_dec(v_u_4152_);
lean_dec_ref(v_h_4098_);
lean_dec(v_a_3976_);
v_a_4229_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4154_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4154_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
else
{
uint8_t v_kind_4237_; 
lean_dec(v_a_4111_);
v_kind_4237_ = lean_ctor_get_uint8(v_c_3853_, sizeof(void*)*5);
if (v_kind_4237_ == 1)
{
lean_object* v_u_4238_; lean_object* v_v_4239_; lean_object* v_k_4240_; lean_object* v___x_4241_; 
v_u_4238_ = lean_ctor_get(v_c_3853_, 0);
lean_inc(v_u_4238_);
v_v_4239_ = lean_ctor_get(v_c_3853_, 1);
lean_inc(v_v_4239_);
v_k_4240_ = lean_ctor_get(v_c_3853_, 2);
lean_inc(v_k_4240_);
lean_dec_ref(v_c_3853_);
v___x_4241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4039_ = v___y_4102_;
v___y_4040_ = v___y_4106_;
v___y_4041_ = v_h_4098_;
v___y_4042_ = v_k_4240_;
v___y_4043_ = v_kind_4237_;
v___y_4044_ = v___y_4109_;
v___y_4045_ = v___y_4099_;
v___y_4046_ = v_u_4238_;
v___y_4047_ = v___y_4103_;
v___y_4048_ = v___y_4104_;
v___y_4049_ = v___y_4101_;
v___y_4050_ = v___y_4100_;
v___y_4051_ = v___y_4105_;
v___y_4052_ = v___y_4108_;
v___y_4053_ = v___y_4107_;
v___y_4054_ = v_v_4239_;
v___y_4055_ = v___x_4241_;
goto v___jp_4038_;
}
else
{
lean_object* v_u_4242_; lean_object* v_v_4243_; lean_object* v_k_4244_; lean_object* v___x_4245_; 
v_u_4242_ = lean_ctor_get(v_c_3853_, 0);
lean_inc(v_u_4242_);
v_v_4243_ = lean_ctor_get(v_c_3853_, 1);
lean_inc(v_v_4243_);
v_k_4244_ = lean_ctor_get(v_c_3853_, 2);
lean_inc(v_k_4244_);
lean_dec_ref(v_c_3853_);
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4039_ = v___y_4102_;
v___y_4040_ = v___y_4106_;
v___y_4041_ = v_h_4098_;
v___y_4042_ = v_k_4244_;
v___y_4043_ = v_kind_4237_;
v___y_4044_ = v___y_4109_;
v___y_4045_ = v___y_4099_;
v___y_4046_ = v_u_4242_;
v___y_4047_ = v___y_4103_;
v___y_4048_ = v___y_4104_;
v___y_4049_ = v___y_4101_;
v___y_4050_ = v___y_4100_;
v___y_4051_ = v___y_4105_;
v___y_4052_ = v___y_4108_;
v___y_4053_ = v___y_4107_;
v___y_4054_ = v_v_4243_;
v___y_4055_ = v___x_4245_;
goto v___jp_4038_;
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec_ref(v_h_4098_);
lean_dec(v_a_3976_);
lean_dec_ref(v_c_3853_);
v_a_4246_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4110_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4110_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
v___jp_4254_:
{
lean_object* v_h_x3f_4266_; 
v_h_x3f_4266_ = lean_ctor_get(v_c_3853_, 4);
if (lean_obj_tag(v_h_x3f_4266_) == 1)
{
lean_object* v_e_4267_; lean_object* v_val_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v_e_4267_ = lean_ctor_get(v_c_3853_, 3);
v_val_4268_ = lean_ctor_get(v_h_x3f_4266_, 0);
v___x_4269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3854_);
v___x_4270_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3854_, v_he_3855_);
lean_inc(v_val_4268_);
lean_inc_ref(v_e_4267_);
v___x_4271_ = l_Lean_mkApp4(v___x_4269_, v_e_3854_, v_e_4267_, v_val_4268_, v___x_4270_);
v_h_4098_ = v___x_4271_;
v___y_4099_ = v___y_4255_;
v___y_4100_ = v___y_4256_;
v___y_4101_ = v___y_4257_;
v___y_4102_ = v___y_4258_;
v___y_4103_ = v___y_4259_;
v___y_4104_ = v___y_4260_;
v___y_4105_ = v___y_4261_;
v___y_4106_ = v___y_4262_;
v___y_4107_ = v___y_4263_;
v___y_4108_ = v___y_4264_;
v___y_4109_ = v___y_4265_;
goto v___jp_4097_;
}
else
{
lean_object* v___x_4272_; 
v___x_4272_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3854_, v_he_3855_);
v_h_4098_ = v___x_4272_;
v___y_4099_ = v___y_4255_;
v___y_4100_ = v___y_4256_;
v___y_4101_ = v___y_4257_;
v___y_4102_ = v___y_4258_;
v___y_4103_ = v___y_4259_;
v___y_4104_ = v___y_4260_;
v___y_4105_ = v___y_4261_;
v___y_4106_ = v___y_4262_;
v___y_4107_ = v___y_4263_;
v___y_4108_ = v___y_4264_;
v___y_4109_ = v___y_4265_;
goto v___jp_4097_;
}
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec_ref(v_he_3855_);
lean_dec_ref(v_e_3854_);
lean_dec_ref(v_c_3853_);
v_a_4298_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_3975_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_3975_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
v___jp_3868_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3885_, 0, v_k_x27_3871_);
lean_ctor_set_uint8(v___x_3885_, sizeof(void*)*1, v_strict_3873_);
v___x_3886_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3870_, v___y_3869_, v___x_3885_, v_h_3872_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
v___jp_3887_:
{
lean_object* v___x_3909_; uint8_t v___x_3910_; 
lean_inc_ref(v___y_3893_);
v___x_3909_ = l_Lean_mkApp6(v___y_3893_, v___y_3888_, v___y_3900_, v___y_3892_, v___y_3908_, v___y_3889_, v___y_3901_);
v___x_3910_ = 0;
v___y_3869_ = v___y_3896_;
v___y_3870_ = v___y_3907_;
v_k_x27_3871_ = v___y_3906_;
v_h_3872_ = v___x_3909_;
v_strict_3873_ = v___x_3910_;
v___y_3874_ = v___y_3895_;
v___y_3875_ = v___y_3902_;
v___y_3876_ = v___y_3899_;
v___y_3877_ = v___y_3890_;
v___y_3878_ = v___y_3897_;
v___y_3879_ = v___y_3898_;
v___y_3880_ = v___y_3903_;
v___y_3881_ = v___y_3891_;
v___y_3882_ = v___y_3905_;
v___y_3883_ = v___y_3904_;
v___y_3884_ = v___y_3894_;
goto v___jp_3868_;
}
v___jp_3911_:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Lean_Meta_Grind_Order_isInt(v___y_3917_, v___y_3924_, v___y_3921_, v___y_3913_, v___y_3919_, v___y_3920_, v___y_3925_, v___y_3914_, v___y_3927_, v___y_3926_, v___y_3916_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; uint8_t v___x_3932_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref_known(v___x_3930_, 1);
v___x_3932_ = lean_unbox(v_a_3931_);
lean_dec(v_a_3931_);
if (v___x_3932_ == 0)
{
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3912_);
v___y_3869_ = v___y_3918_;
v___y_3870_ = v___y_3928_;
v_k_x27_3871_ = v___y_3922_;
v_h_3872_ = v___y_3923_;
v_strict_3873_ = v___y_3929_;
v___y_3874_ = v___y_3917_;
v___y_3875_ = v___y_3924_;
v___y_3876_ = v___y_3921_;
v___y_3877_ = v___y_3913_;
v___y_3878_ = v___y_3919_;
v___y_3879_ = v___y_3920_;
v___y_3880_ = v___y_3925_;
v___y_3881_ = v___y_3914_;
v___y_3882_ = v___y_3927_;
v___y_3883_ = v___y_3926_;
v___y_3884_ = v___y_3916_;
goto v___jp_3868_;
}
else
{
if (v___y_3929_ == 0)
{
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3912_);
v___y_3869_ = v___y_3918_;
v___y_3870_ = v___y_3928_;
v_k_x27_3871_ = v___y_3922_;
v_h_3872_ = v___y_3923_;
v_strict_3873_ = v___y_3929_;
v___y_3874_ = v___y_3917_;
v___y_3875_ = v___y_3924_;
v___y_3876_ = v___y_3921_;
v___y_3877_ = v___y_3913_;
v___y_3878_ = v___y_3919_;
v___y_3879_ = v___y_3920_;
v___y_3880_ = v___y_3925_;
v___y_3881_ = v___y_3914_;
v___y_3882_ = v___y_3927_;
v___y_3883_ = v___y_3926_;
v___y_3884_ = v___y_3916_;
goto v___jp_3868_;
}
else
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3928_, v___y_3917_, v___y_3924_, v___y_3921_, v___y_3913_, v___y_3919_, v___y_3920_, v___y_3925_, v___y_3914_, v___y_3927_, v___y_3926_, v___y_3916_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3935_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
v___x_3935_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3918_, v___y_3917_, v___y_3924_, v___y_3921_, v___y_3913_, v___y_3919_, v___y_3920_, v___y_3925_, v___y_3914_, v___y_3927_, v___y_3926_, v___y_3916_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
v___x_3937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3939_ = lean_int_sub(v___y_3922_, v___x_3938_);
lean_dec(v___y_3922_);
v___x_3940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3941_ = lean_int_dec_le(v___x_3940_, v___x_3939_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3945_ = lean_int_neg(v___x_3939_);
v___x_3946_ = l_Int_toNat(v___x_3945_);
lean_dec(v___x_3945_);
v___x_3947_ = l_Lean_instToExprInt_mkNat(v___x_3946_);
v___x_3948_ = l_Lean_mkApp3(v___x_3942_, v___x_3943_, v___x_3944_, v___x_3947_);
v___y_3888_ = v_a_3934_;
v___y_3889_ = v___y_3912_;
v___y_3890_ = v___y_3913_;
v___y_3891_ = v___y_3914_;
v___y_3892_ = v___y_3915_;
v___y_3893_ = v___x_3937_;
v___y_3894_ = v___y_3916_;
v___y_3895_ = v___y_3917_;
v___y_3896_ = v___y_3918_;
v___y_3897_ = v___y_3919_;
v___y_3898_ = v___y_3920_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v_a_3936_;
v___y_3901_ = v___y_3923_;
v___y_3902_ = v___y_3924_;
v___y_3903_ = v___y_3925_;
v___y_3904_ = v___y_3926_;
v___y_3905_ = v___y_3927_;
v___y_3906_ = v___x_3939_;
v___y_3907_ = v___y_3928_;
v___y_3908_ = v___x_3948_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3949_ = l_Int_toNat(v___x_3939_);
v___x_3950_ = l_Lean_instToExprInt_mkNat(v___x_3949_);
v___y_3888_ = v_a_3934_;
v___y_3889_ = v___y_3912_;
v___y_3890_ = v___y_3913_;
v___y_3891_ = v___y_3914_;
v___y_3892_ = v___y_3915_;
v___y_3893_ = v___x_3937_;
v___y_3894_ = v___y_3916_;
v___y_3895_ = v___y_3917_;
v___y_3896_ = v___y_3918_;
v___y_3897_ = v___y_3919_;
v___y_3898_ = v___y_3920_;
v___y_3899_ = v___y_3921_;
v___y_3900_ = v_a_3936_;
v___y_3901_ = v___y_3923_;
v___y_3902_ = v___y_3924_;
v___y_3903_ = v___y_3925_;
v___y_3904_ = v___y_3926_;
v___y_3905_ = v___y_3927_;
v___y_3906_ = v___x_3939_;
v___y_3907_ = v___y_3928_;
v___y_3908_ = v___x_3950_;
goto v___jp_3887_;
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
lean_dec(v_a_3934_);
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3912_);
v_a_3951_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3935_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3935_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3912_);
v_a_3959_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3933_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3933_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v___y_3928_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3915_);
lean_dec_ref(v___y_3912_);
v_a_3967_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3930_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3930_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4306_, lean_object* v_e_4307_, lean_object* v_he_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4306_, v_e_4307_, v_he_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec(v_a_4309_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4323_, v_a_4324_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4336_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4336_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v_exprToStructId_4331_; lean_object* v___x_4332_; lean_object* v___x_4334_; 
v_exprToStructId_4331_ = lean_ctor_get(v_a_4327_, 2);
lean_inc_ref(v_exprToStructId_4331_);
lean_dec(v_a_4327_);
v___x_4332_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4331_, v_e_4322_);
lean_dec_ref(v_exprToStructId_4331_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4332_);
v___x_4334_ = v___x_4329_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4332_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4326_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4326_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4345_, v_a_4346_, v_a_4347_);
lean_dec_ref(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_e_4345_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
v___x_4362_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4350_, v_a_4351_, v_a_4359_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_);
lean_dec(v_a_4373_);
lean_dec_ref(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
lean_dec(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_e_4363_);
return v_res_4375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = lean_box(0);
v___x_4383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4384_ = l_Lean_mkConst(v___x_4383_, v___x_4382_);
return v___x_4384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4391_ = lean_box(0);
v___x_4392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4393_ = l_Lean_mkConst(v___x_4392_, v___x_4391_);
return v___x_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4394_, lean_object* v_e_x27_4395_, lean_object* v_he_x3f_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4395_, v_a_4397_, v_a_4405_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4499_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4411_ = v___x_4408_;
v_isShared_4412_ = v_isSharedCheck_4499_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4408_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4499_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
if (lean_obj_tag(v_a_4409_) == 1)
{
lean_object* v_val_4413_; lean_object* v___x_4414_; 
lean_del_object(v___x_4411_);
v_val_4413_ = lean_ctor_get(v_a_4409_, 0);
lean_inc(v_val_4413_);
lean_dec_ref_known(v_a_4409_, 1);
v___x_4414_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_x27_4395_, v_val_4413_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4486_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4417_ = v___x_4414_;
v_isShared_4418_ = v_isSharedCheck_4486_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4414_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4486_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
if (lean_obj_tag(v_a_4415_) == 1)
{
lean_object* v_val_4419_; lean_object* v___x_4420_; 
lean_del_object(v___x_4417_);
v_val_4419_ = lean_ctor_get(v_a_4415_, 0);
lean_inc(v_val_4419_);
lean_dec_ref_known(v_a_4415_, 1);
lean_inc_ref(v_e_4394_);
v___x_4420_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4394_, v_a_4397_, v_a_4401_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; uint8_t v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = lean_unbox(v_a_4421_);
lean_dec(v_a_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; 
lean_inc_ref(v_e_4394_);
v___x_4423_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4394_, v_a_4397_, v_a_4401_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4449_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4426_ = v___x_4423_;
v_isShared_4427_ = v_isSharedCheck_4449_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4423_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4449_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
uint8_t v___x_4428_; 
v___x_4428_ = lean_unbox(v_a_4424_);
lean_dec(v_a_4424_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec(v_val_4419_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v___x_4429_ = lean_box(0);
if (v_isShared_4427_ == 0)
{
lean_ctor_set(v___x_4426_, 0, v___x_4429_);
v___x_4431_ = v___x_4426_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
else
{
lean_object* v___x_4433_; 
lean_del_object(v___x_4426_);
lean_inc_ref(v_e_4394_);
v___x_4433_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4394_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4433_) == 0)
{
if (lean_obj_tag(v_he_x3f_4396_) == 1)
{
lean_object* v_a_4434_; lean_object* v_val_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4434_);
lean_dec_ref_known(v___x_4433_, 1);
v_val_4435_ = lean_ctor_get(v_he_x3f_4396_, 0);
lean_inc(v_val_4435_);
lean_dec_ref_known(v_he_x3f_4396_, 1);
v___x_4436_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4395_);
v___x_4437_ = l_Lean_mkApp4(v___x_4436_, v_e_4394_, v_e_x27_4395_, v_val_4435_, v_a_4434_);
v___x_4438_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4419_, v_e_x27_4395_, v___x_4437_, v_val_4413_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_val_4413_);
return v___x_4438_;
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4440_; 
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_4394_);
v_a_4439_ = lean_ctor_get(v___x_4433_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4433_, 1);
v___x_4440_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4419_, v_e_x27_4395_, v_a_4439_, v_val_4413_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_val_4413_);
return v___x_4440_;
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_val_4419_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4441_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4433_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4433_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v_val_4419_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4450_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4423_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4423_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
else
{
lean_object* v___x_4458_; 
lean_inc_ref(v_e_4394_);
v___x_4458_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4394_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4458_) == 0)
{
if (lean_obj_tag(v_he_x3f_4396_) == 1)
{
lean_object* v_a_4459_; lean_object* v_val_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 1);
v_val_4460_ = lean_ctor_get(v_he_x3f_4396_, 0);
lean_inc(v_val_4460_);
lean_dec_ref_known(v_he_x3f_4396_, 1);
v___x_4461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4395_);
v___x_4462_ = l_Lean_mkApp4(v___x_4461_, v_e_4394_, v_e_x27_4395_, v_val_4460_, v_a_4459_);
v___x_4463_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4419_, v_e_x27_4395_, v___x_4462_, v_val_4413_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_val_4413_);
return v___x_4463_;
}
else
{
lean_object* v_a_4464_; lean_object* v___x_4465_; 
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_4394_);
v_a_4464_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4458_, 1);
v___x_4465_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4419_, v_e_x27_4395_, v_a_4464_, v_val_4413_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
lean_dec(v_val_4413_);
return v___x_4465_;
}
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4468_; uint8_t v_isShared_4469_; uint8_t v_isSharedCheck_4473_; 
lean_dec(v_val_4419_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4466_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4468_ = v___x_4458_;
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
else
{
lean_inc(v_a_4466_);
lean_dec(v___x_4458_);
v___x_4468_ = lean_box(0);
v_isShared_4469_ = v_isSharedCheck_4473_;
goto v_resetjp_4467_;
}
v_resetjp_4467_:
{
lean_object* v___x_4471_; 
if (v_isShared_4469_ == 0)
{
v___x_4471_ = v___x_4468_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
v___x_4471_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
return v___x_4471_;
}
}
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4481_; 
lean_dec(v_val_4419_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4474_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4476_ = v___x_4420_;
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v___x_4420_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4481_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v___x_4479_; 
if (v_isShared_4477_ == 0)
{
v___x_4479_ = v___x_4476_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v_a_4474_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
else
{
lean_object* v___x_4482_; lean_object* v___x_4484_; 
lean_dec(v_a_4415_);
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v___x_4482_ = lean_box(0);
if (v_isShared_4418_ == 0)
{
lean_ctor_set(v___x_4417_, 0, v___x_4482_);
v___x_4484_ = v___x_4417_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec(v_val_4413_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4487_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4414_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4414_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
lean_dec(v_a_4409_);
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v___x_4495_ = lean_box(0);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___x_4495_);
v___x_4497_ = v___x_4411_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_he_x3f_4396_);
lean_dec_ref(v_e_x27_4395_);
lean_dec_ref(v_e_4394_);
v_a_4500_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4408_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4408_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4508_, lean_object* v_e_x27_4509_, lean_object* v_he_x3f_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4508_, v_e_x27_4509_, v_he_x3f_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
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
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; 
v___x_4535_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4524_, v_a_4532_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v_termMap_4537_; lean_object* v___x_4538_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v_termMap_4537_ = lean_ctor_get(v_a_4536_, 3);
lean_inc_ref(v_termMap_4537_);
lean_dec(v_a_4536_);
v___x_4538_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4537_, v_e_4523_);
lean_dec_ref(v_termMap_4537_);
if (lean_obj_tag(v___x_4538_) == 1)
{
lean_object* v_val_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4549_; 
v_val_4539_ = lean_ctor_get(v___x_4538_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4541_ = v___x_4538_;
v_isShared_4542_ = v_isSharedCheck_4549_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_val_4539_);
lean_dec(v___x_4538_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4549_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v_e_4543_; lean_object* v_h_4544_; lean_object* v___x_4546_; 
v_e_4543_ = lean_ctor_get(v_val_4539_, 0);
lean_inc_ref(v_e_4543_);
v_h_4544_ = lean_ctor_get(v_val_4539_, 1);
lean_inc_ref(v_h_4544_);
lean_dec(v_val_4539_);
if (v_isShared_4542_ == 0)
{
lean_ctor_set(v___x_4541_, 0, v_h_4544_);
v___x_4546_ = v___x_4541_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_h_4544_);
v___x_4546_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
lean_object* v___x_4547_; 
v___x_4547_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4523_, v_e_4543_, v___x_4546_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4547_;
}
}
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4551_; 
lean_dec(v___x_4538_);
v___x_4550_ = lean_box(0);
lean_inc_ref(v_e_4523_);
v___x_4551_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4523_, v_e_4523_, v___x_4550_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
return v___x_4551_;
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec_ref(v_e_4523_);
v_a_4552_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4535_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4535_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v_a_4570_);
lean_dec(v_a_4570_);
lean_dec_ref(v_a_4569_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec(v_a_4561_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_){
_start:
{
lean_object* v___x_4585_; 
v___x_4585_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_);
return v___x_4585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_);
lean_dec(v_a_4596_);
lean_dec_ref(v_a_4595_);
lean_dec(v_a_4594_);
lean_dec_ref(v_a_4593_);
lean_dec(v_a_4592_);
lean_dec_ref(v_a_4591_);
lean_dec(v_a_4590_);
lean_dec_ref(v_a_4589_);
lean_dec(v_a_4588_);
lean_dec(v_a_4587_);
return v_res_4598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___f_4606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4608_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4607_, v___f_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object* v_a_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_);
return v___x_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec(v_a_4625_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___f_4643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_));
v___x_4645_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4644_, v___f_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_){
_start:
{
lean_object* v___x_4652_; 
v___x_4652_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4649_, v_a_4650_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4662_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4662_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4662_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4662_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v_termMap_4657_; lean_object* v___x_4658_; lean_object* v___x_4660_; 
v_termMap_4657_ = lean_ctor_get(v_a_4653_, 3);
lean_inc_ref(v_termMap_4657_);
lean_dec(v_a_4653_);
v___x_4658_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4657_, v_e_4648_);
lean_dec_ref(v_termMap_4657_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4658_);
v___x_4660_ = v___x_4655_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4661_; 
v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4661_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
return v___x_4660_;
}
}
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v_a_4663_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___x_4652_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4652_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4671_, v_a_4672_, v_a_4673_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_e_4671_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_){
_start:
{
lean_object* v___x_4688_; 
v___x_4688_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4676_, v_a_4677_, v_a_4685_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_);
lean_dec(v_a_4699_);
lean_dec_ref(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_a_4696_);
lean_dec(v_a_4695_);
lean_dec_ref(v_a_4694_);
lean_dec(v_a_4693_);
lean_dec_ref(v_a_4692_);
lean_dec(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_e_4689_);
return v_res_4701_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4726_ = 0;
v___x_4727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4728_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
lean_ctor_set_uint8(v___x_4728_, sizeof(void*)*1, v___x_4726_);
return v___x_4728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4730_; lean_object* v___x_4731_; 
v___x_4730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4731_ = l_Lean_stringToMessageData(v___x_4730_);
return v___x_4731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4732_, lean_object* v_b_4733_, lean_object* v_h_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___x_4845_; 
v___x_4845_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4732_, v_a_4735_, v_a_4743_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4891_; 
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4891_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4891_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
if (lean_obj_tag(v_a_4846_) == 1)
{
lean_object* v_val_4850_; lean_object* v___x_4851_; 
lean_del_object(v___x_4848_);
v_val_4850_ = lean_ctor_get(v_a_4846_, 0);
lean_inc(v_val_4850_);
lean_dec_ref_known(v_a_4846_, 1);
v___x_4851_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4733_, v_a_4735_, v_a_4743_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4878_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4854_ = v___x_4851_;
v_isShared_4855_ = v_isSharedCheck_4878_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4851_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4878_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
if (lean_obj_tag(v_a_4852_) == 1)
{
lean_object* v_val_4856_; uint8_t v___x_4857_; 
v_val_4856_ = lean_ctor_get(v_a_4852_, 0);
lean_inc(v_val_4856_);
lean_dec_ref_known(v_a_4852_, 1);
v___x_4857_ = lean_nat_dec_eq(v_val_4850_, v_val_4856_);
lean_dec(v_val_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4860_; 
lean_dec(v_val_4850_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v___x_4858_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4858_);
v___x_4860_ = v___x_4854_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
else
{
lean_object* v_options_4862_; uint8_t v_hasTrace_4863_; 
lean_del_object(v___x_4854_);
v_options_4862_ = lean_ctor_get(v_a_4743_, 2);
v_hasTrace_4863_ = lean_ctor_get_uint8(v_options_4862_, sizeof(void*)*1);
if (v_hasTrace_4863_ == 0)
{
v___y_4747_ = v_val_4850_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
v___y_4753_ = v_a_4740_;
v___y_4754_ = v_a_4741_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
goto v___jp_4746_;
}
else
{
lean_object* v_inheritedTraceOptions_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; 
v_inheritedTraceOptions_4864_ = lean_ctor_get(v_a_4743_, 13);
v___x_4865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4866_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4864_, v_options_4862_, v___x_4866_);
if (v___x_4867_ == 0)
{
v___y_4747_ = v_val_4850_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
v___y_4753_ = v_a_4740_;
v___y_4754_ = v_a_4741_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
goto v___jp_4746_;
}
else
{
lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
lean_inc_ref(v_a_4732_);
v___x_4868_ = l_Lean_MessageData_ofExpr(v_a_4732_);
v___x_4869_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4869_);
lean_inc_ref(v_b_4733_);
v___x_4871_ = l_Lean_MessageData_ofExpr(v_b_4733_);
v___x_4872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4870_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4865_, v___x_4872_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_dec_ref_known(v___x_4873_, 1);
v___y_4747_ = v_val_4850_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
v___y_4753_ = v_a_4740_;
v___y_4754_ = v_a_4741_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
goto v___jp_4746_;
}
else
{
lean_dec(v_val_4850_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
return v___x_4873_;
}
}
}
}
}
else
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
lean_dec(v_a_4852_);
lean_dec(v_val_4850_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v___x_4874_ = lean_box(0);
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4874_);
v___x_4876_ = v___x_4854_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec(v_val_4850_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4879_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4851_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4851_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
lean_dec(v_a_4846_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v___x_4887_ = lean_box(0);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 0, v___x_4887_);
v___x_4889_ = v___x_4848_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4892_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4845_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4845_);
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
v___jp_4746_:
{
lean_object* v___x_4758_; 
lean_inc_ref(v_a_4732_);
v___x_4758_ = l_Lean_Meta_Grind_Order_getNodeId(v_a_4732_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4758_) == 0)
{
lean_object* v_a_4759_; lean_object* v___x_4760_; 
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
lean_inc(v_a_4759_);
lean_dec_ref_known(v___x_4758_, 1);
lean_inc_ref(v_b_4733_);
v___x_4760_ = l_Lean_Meta_Grind_Order_getNodeId(v_b_4733_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4762_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v___x_4762_ = l_Lean_Meta_Grind_Order_isRing(v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4762_) == 0)
{
lean_object* v_a_4763_; uint8_t v___x_4764_; 
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref_known(v___x_4762_, 1);
v___x_4764_ = lean_unbox(v_a_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4766_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4765_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref_known(v___x_4766_, 1);
v___x_4768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4769_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4768_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
lean_inc_ref(v_h_4734_);
lean_inc_ref(v_b_4733_);
lean_inc_ref(v_a_4732_);
v___x_4771_ = l_Lean_mkApp3(v_a_4767_, v_a_4732_, v_b_4733_, v_h_4734_);
v___x_4772_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4773_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4773_, 0, v___x_4772_);
v___x_4774_ = lean_unbox(v_a_4763_);
lean_dec(v_a_4763_);
lean_ctor_set_uint8(v___x_4773_, sizeof(void*)*1, v___x_4774_);
lean_inc_ref(v___x_4773_);
lean_inc(v_a_4761_);
lean_inc(v_a_4759_);
v___x_4775_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4759_, v_a_4761_, v___x_4773_, v___x_4771_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
lean_dec_ref_known(v___x_4775_, 1);
v___x_4776_ = l_Lean_mkApp3(v_a_4770_, v_a_4732_, v_b_4733_, v_h_4734_);
v___x_4777_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4761_, v_a_4759_, v___x_4773_, v___x_4776_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4747_);
return v___x_4777_;
}
else
{
lean_dec_ref_known(v___x_4773_, 1);
lean_dec(v_a_4770_);
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
return v___x_4775_;
}
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
lean_dec(v_a_4767_);
lean_dec(v_a_4763_);
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4778_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___x_4769_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___x_4769_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
else
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4793_; 
lean_dec(v_a_4763_);
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4786_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4788_ = v___x_4766_;
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4766_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4793_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4792_; 
v_reuseFailAlloc_4792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_a_4786_);
v___x_4791_ = v_reuseFailAlloc_4792_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
return v___x_4791_;
}
}
}
}
else
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
lean_dec(v_a_4763_);
v___x_4794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4795_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4794_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v___x_4797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4798_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4797_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_object* v_a_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v_a_4799_ = lean_ctor_get(v___x_4798_, 0);
lean_inc(v_a_4799_);
lean_dec_ref_known(v___x_4798_, 1);
lean_inc_ref(v_h_4734_);
lean_inc_ref(v_b_4733_);
lean_inc_ref(v_a_4732_);
v___x_4800_ = l_Lean_mkApp3(v_a_4796_, v_a_4732_, v_b_4733_, v_h_4734_);
v___x_4801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4761_);
lean_inc(v_a_4759_);
v___x_4802_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4759_, v_a_4761_, v___x_4801_, v___x_4800_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
lean_dec_ref_known(v___x_4802_, 1);
v___x_4803_ = l_Lean_mkApp3(v_a_4799_, v_a_4732_, v_b_4733_, v_h_4734_);
v___x_4804_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4761_, v_a_4759_, v___x_4801_, v___x_4803_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
lean_dec(v___y_4747_);
return v___x_4804_;
}
else
{
lean_dec(v_a_4799_);
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
return v___x_4802_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec(v_a_4796_);
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4805_ = lean_ctor_get(v___x_4798_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4798_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4798_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4798_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4813_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4795_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4795_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec(v_a_4761_);
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4821_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4762_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4762_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec(v_a_4759_);
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4829_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4760_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4760_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec(v___y_4747_);
lean_dec_ref(v_h_4734_);
lean_dec_ref(v_b_4733_);
lean_dec_ref(v_a_4732_);
v_a_4837_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4758_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4758_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4900_, lean_object* v_b_4901_, lean_object* v_h_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4900_, v_b_4901_, v_h_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_);
lean_dec(v_a_4912_);
lean_dec_ref(v_a_4911_);
lean_dec(v_a_4910_);
lean_dec_ref(v_a_4909_);
lean_dec(v_a_4908_);
lean_dec_ref(v_a_4907_);
lean_dec(v_a_4906_);
lean_dec_ref(v_a_4905_);
lean_dec(v_a_4904_);
lean_dec(v_a_4903_);
return v_res_4914_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v___x_4930_ = lean_box(0);
v___x_4931_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4932_ = l_Lean_mkConst(v___x_4931_, v___x_4930_);
return v___x_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4933_, lean_object* v_b_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
size_t v___x_4946_; size_t v___x_4947_; uint8_t v___x_4948_; 
v___x_4946_ = lean_ptr_addr(v_a_4933_);
v___x_4947_ = lean_ptr_addr(v_b_4934_);
v___x_4948_ = lean_usize_dec_eq(v___x_4946_, v___x_4947_);
if (v___x_4948_ == 0)
{
lean_object* v___x_4949_; 
lean_inc(v_a_4944_);
lean_inc_ref(v_a_4943_);
lean_inc(v_a_4942_);
lean_inc_ref(v_a_4941_);
lean_inc(v_a_4940_);
lean_inc_ref(v_a_4939_);
lean_inc(v_a_4938_);
lean_inc_ref(v_a_4937_);
lean_inc(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v_b_4934_);
lean_inc_ref(v_a_4933_);
v___x_4949_ = lean_grind_mk_eq_proof(v_a_4933_, v_b_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4951_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
lean_inc(v_a_4950_);
lean_dec_ref_known(v___x_4949_, 1);
v___x_4951_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4933_, v_a_4935_, v_a_4943_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v_a_4952_; 
v_a_4952_ = lean_ctor_get(v___x_4951_, 0);
lean_inc(v_a_4952_);
lean_dec_ref_known(v___x_4951_, 1);
if (lean_obj_tag(v_a_4952_) == 1)
{
lean_object* v_val_4953_; lean_object* v_e_4954_; lean_object* v_h_4955_; lean_object* v_00_u03b1_4956_; lean_object* v___x_4957_; 
v_val_4953_ = lean_ctor_get(v_a_4952_, 0);
lean_inc(v_val_4953_);
lean_dec_ref_known(v_a_4952_, 1);
v_e_4954_ = lean_ctor_get(v_val_4953_, 0);
lean_inc_ref(v_e_4954_);
v_h_4955_ = lean_ctor_get(v_val_4953_, 1);
lean_inc_ref(v_h_4955_);
v_00_u03b1_4956_ = lean_ctor_get(v_val_4953_, 2);
lean_inc_ref(v_00_u03b1_4956_);
lean_dec(v_val_4953_);
v___x_4957_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4934_, v_a_4935_, v_a_4943_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_5003_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4960_ = v___x_4957_;
v_isShared_4961_ = v_isSharedCheck_5003_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_a_4958_);
lean_dec(v___x_4957_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_5003_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
if (lean_obj_tag(v_a_4958_) == 1)
{
lean_object* v_val_4962_; lean_object* v_e_4963_; lean_object* v_h_4964_; lean_object* v___x_4965_; uint8_t v___x_4966_; 
lean_del_object(v___x_4960_);
v_val_4962_ = lean_ctor_get(v_a_4958_, 0);
lean_inc(v_val_4962_);
lean_dec_ref_known(v_a_4958_, 1);
v_e_4963_ = lean_ctor_get(v_val_4962_, 0);
lean_inc_ref(v_e_4963_);
v_h_4964_ = lean_ctor_get(v_val_4962_, 1);
lean_inc_ref(v_h_4964_);
lean_dec(v_val_4962_);
v___x_4965_ = l_Lean_Int_mkType;
v___x_4966_ = lean_expr_eqv(v_00_u03b1_4956_, v___x_4965_);
if (v___x_4966_ == 0)
{
lean_object* v___x_4967_; 
lean_inc_ref(v_00_u03b1_4956_);
v___x_4967_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4956_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4969_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4970_ = lean_box(0);
v___x_4971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4971_, 0, v_a_4968_);
lean_ctor_set(v___x_4971_, 1, v___x_4970_);
lean_inc_ref(v___x_4971_);
v___x_4972_ = l_Lean_mkConst(v___x_4969_, v___x_4971_);
lean_inc_ref(v_00_u03b1_4956_);
v___x_4973_ = l_Lean_Expr_app___override(v___x_4972_, v_00_u03b1_4956_);
v___x_4974_ = l_Lean_Meta_Sym_synthInstance(v___x_4973_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
if (lean_obj_tag(v___x_4974_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v_a_4975_ = lean_ctor_get(v___x_4974_, 0);
lean_inc(v_a_4975_);
lean_dec_ref_known(v___x_4974_, 1);
v___x_4976_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_4977_ = l_Lean_mkConst(v___x_4976_, v___x_4971_);
lean_inc_ref(v_e_4963_);
lean_inc_ref(v_e_4954_);
v___x_4978_ = l_Lean_mkApp9(v___x_4977_, v_00_u03b1_4956_, v_a_4975_, v_a_4933_, v_b_4934_, v_e_4954_, v_e_4963_, v_h_4955_, v_h_4964_, v_a_4950_);
v___x_4979_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4954_, v_e_4963_, v___x_4978_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v___x_4979_;
}
else
{
lean_object* v_a_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4987_; 
lean_dec_ref_known(v___x_4971_, 2);
lean_dec_ref(v_h_4964_);
lean_dec_ref(v_e_4963_);
lean_dec_ref(v_00_u03b1_4956_);
lean_dec_ref(v_h_4955_);
lean_dec_ref(v_e_4954_);
lean_dec(v_a_4950_);
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v_a_4980_ = lean_ctor_get(v___x_4974_, 0);
v_isSharedCheck_4987_ = !lean_is_exclusive(v___x_4974_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4982_ = v___x_4974_;
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_a_4980_);
lean_dec(v___x_4974_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4987_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4985_; 
if (v_isShared_4983_ == 0)
{
v___x_4985_ = v___x_4982_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4980_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
return v___x_4985_;
}
}
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_dec_ref(v_h_4964_);
lean_dec_ref(v_e_4963_);
lean_dec_ref(v_00_u03b1_4956_);
lean_dec_ref(v_h_4955_);
lean_dec_ref(v_e_4954_);
lean_dec(v_a_4950_);
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v_a_4988_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4967_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4967_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_dec_ref(v_00_u03b1_4956_);
v___x_4996_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_4963_);
lean_inc_ref(v_e_4954_);
v___x_4997_ = l_Lean_mkApp7(v___x_4996_, v_a_4933_, v_b_4934_, v_e_4954_, v_e_4963_, v_h_4955_, v_h_4964_, v_a_4950_);
v___x_4998_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4954_, v_e_4963_, v___x_4997_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v___x_4998_;
}
}
else
{
lean_object* v___x_4999_; lean_object* v___x_5001_; 
lean_dec(v_a_4958_);
lean_dec_ref(v_00_u03b1_4956_);
lean_dec_ref(v_h_4955_);
lean_dec_ref(v_e_4954_);
lean_dec(v_a_4950_);
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v___x_4999_ = lean_box(0);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4999_);
v___x_5001_ = v___x_4960_;
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
lean_dec_ref(v_00_u03b1_4956_);
lean_dec_ref(v_h_4955_);
lean_dec_ref(v_e_4954_);
lean_dec(v_a_4950_);
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v_a_5004_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4957_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4957_);
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
}
else
{
lean_object* v___x_5012_; 
lean_dec(v_a_4952_);
v___x_5012_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4933_, v_b_4934_, v_a_4950_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_);
return v___x_5012_;
}
}
else
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5020_; 
lean_dec(v_a_4950_);
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v_a_5013_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_5020_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_5020_ == 0)
{
v___x_5015_ = v___x_4951_;
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v___x_4951_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5020_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5018_; 
if (v_isShared_5016_ == 0)
{
v___x_5018_ = v___x_5015_;
goto v_reusejp_5017_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_a_5013_);
v___x_5018_ = v_reuseFailAlloc_5019_;
goto v_reusejp_5017_;
}
v_reusejp_5017_:
{
return v___x_5018_;
}
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v_a_5021_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4949_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4949_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
lean_dec_ref(v_b_4934_);
lean_dec_ref(v_a_4933_);
v___x_5029_ = lean_box(0);
v___x_5030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
return v___x_5030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5031_, lean_object* v_b_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5031_, v_b_5032_, v_a_5033_, v_a_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_, v_a_5041_, v_a_5042_);
lean_dec(v_a_5042_);
lean_dec_ref(v_a_5041_);
lean_dec(v_a_5040_);
lean_dec_ref(v_a_5039_);
lean_dec(v_a_5038_);
lean_dec_ref(v_a_5037_);
lean_dec(v_a_5036_);
lean_dec_ref(v_a_5035_);
lean_dec(v_a_5034_);
lean_dec(v_a_5033_);
return v_res_5044_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_OrderM(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Order(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Proof(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order_Assert(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
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
