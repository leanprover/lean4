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
lean_object* v___x_892_; lean_object* v_env_893_; lean_object* v___x_894_; lean_object* v_toCold_895_; lean_object* v_mctx_896_; lean_object* v_lctx_897_; lean_object* v_options_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_892_ = lean_st_ref_get(v___y_890_);
v_env_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_893_);
lean_dec(v___x_892_);
v___x_894_ = lean_st_ref_get(v___y_888_);
v_toCold_895_ = lean_ctor_get(v___y_889_, 0);
v_mctx_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc_ref(v_mctx_896_);
lean_dec(v___x_894_);
v_lctx_897_ = lean_ctor_get(v___y_887_, 2);
v_options_898_ = lean_ctor_get(v_toCold_895_, 2);
lean_inc_ref(v_options_898_);
lean_inc_ref(v_lctx_897_);
v___x_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_899_, 0, v_env_893_);
lean_ctor_set(v___x_899_, 1, v_mctx_896_);
lean_ctor_set(v___x_899_, 2, v_lctx_897_);
lean_ctor_set(v___x_899_, 3, v_options_898_);
v___x_900_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v_msgData_886_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_909_; double v___x_910_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_float_of_nat(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_914_, lean_object* v_msg_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_ref_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_967_; 
v_ref_921_ = lean_ctor_get(v___y_918_, 2);
v___x_922_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_967_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_967_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_967_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v_traceState_928_; lean_object* v_env_929_; lean_object* v_nextMacroScope_930_; lean_object* v_ngen_931_; lean_object* v_auxDeclNGen_932_; lean_object* v_cache_933_; lean_object* v_messages_934_; lean_object* v_infoState_935_; lean_object* v_snapshotTasks_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_966_; 
v___x_927_ = lean_st_ref_take(v___y_919_);
v_traceState_928_ = lean_ctor_get(v___x_927_, 4);
v_env_929_ = lean_ctor_get(v___x_927_, 0);
v_nextMacroScope_930_ = lean_ctor_get(v___x_927_, 1);
v_ngen_931_ = lean_ctor_get(v___x_927_, 2);
v_auxDeclNGen_932_ = lean_ctor_get(v___x_927_, 3);
v_cache_933_ = lean_ctor_get(v___x_927_, 5);
v_messages_934_ = lean_ctor_get(v___x_927_, 6);
v_infoState_935_ = lean_ctor_get(v___x_927_, 7);
v_snapshotTasks_936_ = lean_ctor_get(v___x_927_, 8);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_966_ == 0)
{
v___x_938_ = v___x_927_;
v_isShared_939_ = v_isSharedCheck_966_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snapshotTasks_936_);
lean_inc(v_infoState_935_);
lean_inc(v_messages_934_);
lean_inc(v_cache_933_);
lean_inc(v_traceState_928_);
lean_inc(v_auxDeclNGen_932_);
lean_inc(v_ngen_931_);
lean_inc(v_nextMacroScope_930_);
lean_inc(v_env_929_);
lean_dec(v___x_927_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_966_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
uint64_t v_tid_940_; lean_object* v_traces_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_965_; 
v_tid_940_ = lean_ctor_get_uint64(v_traceState_928_, sizeof(void*)*1);
v_traces_941_ = lean_ctor_get(v_traceState_928_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_traceState_928_);
if (v_isSharedCheck_965_ == 0)
{
v___x_943_ = v_traceState_928_;
v_isShared_944_ = v_isSharedCheck_965_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_traces_941_);
lean_dec(v_traceState_928_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_965_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; double v___x_946_; uint8_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_945_ = lean_box(0);
v___x_946_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_947_ = 0;
v___x_948_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_949_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_949_, 0, v_cls_914_);
lean_ctor_set(v___x_949_, 1, v___x_945_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
lean_ctor_set_float(v___x_949_, sizeof(void*)*3, v___x_946_);
lean_ctor_set_float(v___x_949_, sizeof(void*)*3 + 8, v___x_946_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*3 + 16, v___x_947_);
v___x_950_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_951_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_951_, 0, v___x_949_);
lean_ctor_set(v___x_951_, 1, v_a_923_);
lean_ctor_set(v___x_951_, 2, v___x_950_);
lean_inc(v_ref_921_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v_ref_921_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_PersistentArray_push___redArg(v_traces_941_, v___x_952_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_953_);
v___x_955_ = v___x_943_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_953_);
lean_ctor_set_uint64(v_reuseFailAlloc_964_, sizeof(void*)*1, v_tid_940_);
v___x_955_ = v_reuseFailAlloc_964_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v___x_955_);
v___x_957_ = v___x_938_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_env_929_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v_nextMacroScope_930_);
lean_ctor_set(v_reuseFailAlloc_963_, 2, v_ngen_931_);
lean_ctor_set(v_reuseFailAlloc_963_, 3, v_auxDeclNGen_932_);
lean_ctor_set(v_reuseFailAlloc_963_, 4, v___x_955_);
lean_ctor_set(v_reuseFailAlloc_963_, 5, v_cache_933_);
lean_ctor_set(v_reuseFailAlloc_963_, 6, v_messages_934_);
lean_ctor_set(v_reuseFailAlloc_963_, 7, v_infoState_935_);
lean_ctor_set(v_reuseFailAlloc_963_, 8, v_snapshotTasks_936_);
v___x_957_ = v_reuseFailAlloc_963_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_958_ = lean_st_ref_put(v___y_919_, v___x_957_);
v___x_959_ = lean_box(0);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_959_);
v___x_961_ = v___x_925_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_968_, v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_cls_988_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_990_ = l_Lean_Name_append(v___x_989_, v_cls_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_toCold_1004_; lean_object* v_options_1005_; lean_object* v_inheritedTraceOptions_1006_; uint8_t v_hasTrace_1007_; lean_object* v___f_1008_; 
v_toCold_1004_ = lean_ctor_get(v_a_1001_, 0);
v_options_1005_ = lean_ctor_get(v_toCold_1004_, 2);
v_inheritedTraceOptions_1006_ = lean_ctor_get(v_toCold_1004_, 11);
v_hasTrace_1007_ = lean_ctor_get_uint8(v_options_1005_, sizeof(void*)*1);
lean_inc_ref(v_p_991_);
v___f_1008_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_1008_, 0, v_p_991_);
if (v_hasTrace_1007_ == 0)
{
lean_object* v___x_1009_; 
lean_dec_ref(v_p_991_);
v___x_1009_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1008_, v_a_992_, v_a_993_);
return v___x_1009_;
}
else
{
lean_object* v_cls_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_cls_1010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_1011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7);
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1006_, v_options_1005_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; 
lean_dec_ref(v_p_991_);
v___x_1013_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1008_, v_a_992_, v_a_993_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_p_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1010_, v_a_1015_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1008_, v_a_992_, v_a_993_);
return v___x_1017_;
}
else
{
lean_dec_ref(v___f_1008_);
return v___x_1016_;
}
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v___f_1008_);
v_a_1018_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1014_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1014_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec(v_a_1027_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_1040_, lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1040_, v_msg_1041_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1055_, v_msg_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
lean_dec_ref(v___y_1062_);
lean_dec(v___y_1061_);
lean_dec_ref(v___y_1060_);
lean_dec(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec(v___y_1057_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_i_1072_, lean_object* v_k_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_array_get_size(v_keys_1070_);
v___x_1075_ = lean_nat_dec_lt(v_i_1072_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v_i_1072_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
else
{
lean_object* v_k_x27_1077_; size_t v___x_1078_; size_t v___x_1079_; uint8_t v___x_1080_; 
v_k_x27_1077_ = lean_array_fget_borrowed(v_keys_1070_, v_i_1072_);
v___x_1078_ = lean_ptr_addr(v_k_1073_);
v___x_1079_ = lean_ptr_addr(v_k_x27_1077_);
v___x_1080_ = lean_usize_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = lean_nat_add(v_i_1072_, v___x_1081_);
lean_dec(v_i_1072_);
v_i_1072_ = v___x_1082_;
goto _start;
}
else
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_array_fget_borrowed(v_vals_1071_, v_i_1072_);
lean_dec(v_i_1072_);
lean_inc(v___x_1084_);
v___x_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1086_, lean_object* v_vals_1087_, lean_object* v_i_1088_, lean_object* v_k_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1086_, v_vals_1087_, v_i_1088_, v_k_1089_);
lean_dec_ref(v_k_1089_);
lean_dec_ref(v_vals_1087_);
lean_dec_ref(v_keys_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1091_, size_t v_x_1092_, lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1091_) == 0)
{
lean_object* v_es_1094_; lean_object* v___x_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v_j_1098_; lean_object* v___x_1099_; 
v_es_1094_ = lean_ctor_get(v_x_1091_, 0);
v___x_1095_ = lean_box(2);
v___x_1096_ = ((size_t)31ULL);
v___x_1097_ = lean_usize_land(v_x_1092_, v___x_1096_);
v_j_1098_ = lean_usize_to_nat(v___x_1097_);
v___x_1099_ = lean_array_get_borrowed(v___x_1095_, v_es_1094_, v_j_1098_);
lean_dec(v_j_1098_);
switch(lean_obj_tag(v___x_1099_))
{
case 0:
{
lean_object* v_key_1100_; lean_object* v_val_1101_; size_t v___x_1102_; size_t v___x_1103_; uint8_t v___x_1104_; 
v_key_1100_ = lean_ctor_get(v___x_1099_, 0);
v_val_1101_ = lean_ctor_get(v___x_1099_, 1);
v___x_1102_ = lean_ptr_addr(v_x_1093_);
v___x_1103_ = lean_ptr_addr(v_key_1100_);
v___x_1104_ = lean_usize_dec_eq(v___x_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_box(0);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; 
lean_inc(v_val_1101_);
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_val_1101_);
return v___x_1106_;
}
}
case 1:
{
lean_object* v_node_1107_; size_t v___x_1108_; size_t v___x_1109_; 
v_node_1107_ = lean_ctor_get(v___x_1099_, 0);
v___x_1108_ = ((size_t)5ULL);
v___x_1109_ = lean_usize_shift_right(v_x_1092_, v___x_1108_);
v_x_1091_ = v_node_1107_;
v_x_1092_ = v___x_1109_;
goto _start;
}
default: 
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
}
}
else
{
lean_object* v_ks_1112_; lean_object* v_vs_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_ks_1112_ = lean_ctor_get(v_x_1091_, 0);
v_vs_1113_ = lean_ctor_get(v_x_1091_, 1);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1112_, v_vs_1113_, v___x_1114_, v_x_1093_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
size_t v_x_9896__boxed_1119_; lean_object* v_res_1120_; 
v_x_9896__boxed_1119_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_res_1120_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1116_, v_x_9896__boxed_1119_, v_x_1118_);
lean_dec_ref(v_x_1118_);
lean_dec_ref(v_x_1116_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
size_t v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; uint64_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___x_1123_ = lean_ptr_addr(v_x_1122_);
v___x_1124_ = ((size_t)3ULL);
v___x_1125_ = lean_usize_shift_right(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_usize_to_uint64(v___x_1125_);
v___x_1127_ = lean_uint64_to_usize(v___x_1126_);
v___x_1128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1121_, v___x_1127_, v_x_1122_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1129_, v_x_1130_);
lean_dec_ref(v_x_1130_);
lean_dec_ref(v_x_1129_);
return v_res_1131_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1143_ = l_Lean_mkConst(v___x_1142_, v___x_1141_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1144_, lean_object* v_e_1145_, lean_object* v_u_1146_, lean_object* v_v_1147_, lean_object* v_k_1148_, lean_object* v_k_x27_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_h_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1146_, v_v_1147_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1146_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1147_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v___x_1196_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1193_, v_a_1195_, v_k_1148_, v_a_1191_, v_k_x27_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_h_x3f_1197_; 
v_h_x3f_1197_ = lean_ctor_get(v_c_1144_, 4);
lean_inc(v_h_x3f_1197_);
if (lean_obj_tag(v_h_x3f_1197_) == 1)
{
lean_object* v_a_1198_; lean_object* v_e_1199_; lean_object* v_val_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_a_1198_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1196_, 1);
v_e_1199_ = lean_ctor_get(v_c_1144_, 3);
lean_inc_ref(v_e_1199_);
lean_dec_ref(v_c_1144_);
v_val_1200_ = lean_ctor_get(v_h_x3f_1197_, 0);
lean_inc(v_val_1200_);
lean_dec_ref_known(v_h_x3f_1197_, 1);
v___x_1201_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1145_);
v___x_1202_ = l_Lean_mkApp4(v___x_1201_, v_e_1145_, v_e_1199_, v_val_1200_, v_a_1198_);
v_h_1163_ = v___x_1202_;
v___y_1164_ = v_a_1151_;
v___y_1165_ = v_a_1153_;
v___y_1166_ = v_a_1155_;
v___y_1167_ = v_a_1157_;
v___y_1168_ = v_a_1158_;
v___y_1169_ = v_a_1159_;
v___y_1170_ = v_a_1160_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1203_; 
lean_dec(v_h_x3f_1197_);
lean_dec_ref(v_c_1144_);
v_a_1203_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1196_, 1);
v_h_1163_ = v_a_1203_;
v___y_1164_ = v_a_1151_;
v___y_1165_ = v_a_1153_;
v___y_1166_ = v_a_1155_;
v___y_1167_ = v_a_1157_;
v___y_1168_ = v_a_1158_;
v___y_1169_ = v_a_1159_;
v___y_1170_ = v_a_1160_;
goto v___jp_1162_;
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_e_1145_);
lean_dec_ref(v_c_1144_);
v_a_1204_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1196_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1196_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_a_1193_);
lean_dec(v_a_1191_);
lean_dec_ref(v_e_1145_);
lean_dec_ref(v_c_1144_);
v_a_1212_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1194_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1194_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
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
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_a_1191_);
lean_dec_ref(v_e_1145_);
lean_dec_ref(v_c_1144_);
v_a_1220_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1192_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1192_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_e_1145_);
lean_dec_ref(v_c_1144_);
v_a_1228_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1190_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1190_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
v___jp_1162_:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1164_, v___y_1169_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_termMapInv_1173_; lean_object* v___x_1174_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v_termMapInv_1173_ = lean_ctor_get(v_a_1172_, 4);
lean_inc_ref(v_termMapInv_1173_);
lean_dec(v_a_1172_);
v___x_1174_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1173_, v_e_1145_);
lean_dec_ref(v_termMapInv_1173_);
if (lean_obj_tag(v___x_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_val_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_fst_1176_ = lean_ctor_get(v_val_1175_, 0);
lean_inc_n(v_fst_1176_, 2);
v_snd_1177_ = lean_ctor_get(v_val_1175_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_val_1175_);
v___x_1178_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1179_ = l_Lean_mkApp4(v___x_1178_, v_fst_1176_, v_e_1145_, v_snd_1177_, v_h_1163_);
v___x_1180_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1176_, v___x_1179_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1180_;
}
else
{
lean_object* v___x_1181_; 
lean_dec(v___x_1174_);
v___x_1181_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1145_, v_h_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
return v___x_1181_;
}
}
else
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_e_1145_);
v_a_1182_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1184_ = v___x_1171_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1171_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_a_1182_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1236_ = _args[0];
lean_object* v_e_1237_ = _args[1];
lean_object* v_u_1238_ = _args[2];
lean_object* v_v_1239_ = _args[3];
lean_object* v_k_1240_ = _args[4];
lean_object* v_k_x27_1241_ = _args[5];
lean_object* v_a_1242_ = _args[6];
lean_object* v_a_1243_ = _args[7];
lean_object* v_a_1244_ = _args[8];
lean_object* v_a_1245_ = _args[9];
lean_object* v_a_1246_ = _args[10];
lean_object* v_a_1247_ = _args[11];
lean_object* v_a_1248_ = _args[12];
lean_object* v_a_1249_ = _args[13];
lean_object* v_a_1250_ = _args[14];
lean_object* v_a_1251_ = _args[15];
lean_object* v_a_1252_ = _args[16];
lean_object* v_a_1253_ = _args[17];
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1236_, v_e_1237_, v_u_1238_, v_v_1239_, v_k_1240_, v_k_x27_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec_ref(v_a_1249_);
lean_dec(v_a_1248_);
lean_dec_ref(v_a_1247_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_k_x27_1241_);
lean_dec_ref(v_k_1240_);
lean_dec(v_v_1239_);
lean_dec(v_u_1238_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1256_, v_x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1259_, v_x_1260_, v_x_1261_);
lean_dec_ref(v_x_1261_);
lean_dec_ref(v_x_1260_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1263_, lean_object* v_x_1264_, size_t v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1264_, v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
size_t v_x_10164__boxed_1272_; lean_object* v_res_1273_; 
v_x_10164__boxed_1272_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_res_1273_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1268_, v_x_1269_, v_x_10164__boxed_1272_, v_x_1271_);
lean_dec_ref(v_x_1271_);
lean_dec_ref(v_x_1269_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1274_, lean_object* v_keys_1275_, lean_object* v_vals_1276_, lean_object* v_heq_1277_, lean_object* v_i_1278_, lean_object* v_k_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1275_, v_vals_1276_, v_i_1278_, v_k_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1281_, lean_object* v_keys_1282_, lean_object* v_vals_1283_, lean_object* v_heq_1284_, lean_object* v_i_1285_, lean_object* v_k_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1281_, v_keys_1282_, v_vals_1283_, v_heq_1284_, v_i_1285_, v_k_1286_);
lean_dec_ref(v_k_1286_);
lean_dec_ref(v_vals_1283_);
lean_dec_ref(v_keys_1282_);
return v_res_1287_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___f_1303_; lean_object* v___x_5398__overap_1304_; lean_object* v___x_1305_; 
v___x_1302_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1303_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1303_, 0, v___x_1302_);
v___x_5398__overap_1304_ = lean_panic_fn_borrowed(v___f_1303_, v_msg_1289_);
lean_dec_ref(v___f_1303_);
lean_inc(v___y_1300_);
lean_inc_ref(v___y_1299_);
lean_inc(v___y_1298_);
lean_inc_ref(v___y_1297_);
lean_inc(v___y_1296_);
lean_inc_ref(v___y_1295_);
lean_inc(v___y_1294_);
lean_inc_ref(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc(v___y_1291_);
lean_inc(v___y_1290_);
v___x_1305_ = lean_apply_12(v___x_5398__overap_1304_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, lean_box(0));
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
lean_dec(v___y_1317_);
lean_dec_ref(v___y_1316_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1319_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1324_ = lean_unsigned_to_nat(2u);
v___x_1325_ = lean_unsigned_to_nat(86u);
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1328_ = l_mkPanicMessageWithDecl(v___x_1327_, v___x_1326_, v___x_1325_, v___x_1324_, v___x_1323_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1329_, lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_u_1343_; lean_object* v_v_1344_; lean_object* v_e_1345_; lean_object* v_h_x3f_1346_; lean_object* v___x_1347_; 
v_u_1343_ = lean_ctor_get(v_c_1329_, 0);
v_v_1344_ = lean_ctor_get(v_c_1329_, 1);
v_e_1345_ = lean_ctor_get(v_c_1329_, 3);
lean_inc_ref(v_e_1345_);
v_h_x3f_1346_ = lean_ctor_get(v_c_1329_, 4);
lean_inc(v_h_x3f_1346_);
v___x_1347_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; uint8_t v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = lean_nat_dec_eq(v_u_1343_, v_v_1344_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_a_1348_);
lean_dec(v_h_x3f_1346_);
lean_dec_ref(v_e_1345_);
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_c_1329_);
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1351_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1350_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
return v___x_1351_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1329_);
lean_dec_ref(v_c_1329_);
v___x_1353_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1348_, v___x_1352_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
lean_dec_ref(v___x_1352_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v_h_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref_known(v___x_1353_, 1);
if (lean_obj_tag(v_h_x3f_1346_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_val_1383_ = lean_ctor_get(v_h_x3f_1346_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_h_x3f_1346_, 1);
v___x_1384_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1330_);
v___x_1385_ = l_Lean_mkApp4(v___x_1384_, v_e_1330_, v_e_1345_, v_val_1383_, v_a_1354_);
v_h_1356_ = v___x_1385_;
v___y_1357_ = v_a_1332_;
v___y_1358_ = v_a_1334_;
v___y_1359_ = v_a_1336_;
v___y_1360_ = v_a_1338_;
v___y_1361_ = v_a_1339_;
v___y_1362_ = v_a_1340_;
v___y_1363_ = v_a_1341_;
goto v___jp_1355_;
}
else
{
lean_dec(v_h_x3f_1346_);
lean_dec_ref(v_e_1345_);
v_h_1356_ = v_a_1354_;
v___y_1357_ = v_a_1332_;
v___y_1358_ = v_a_1334_;
v___y_1359_ = v_a_1336_;
v___y_1360_ = v_a_1338_;
v___y_1361_ = v_a_1339_;
v___y_1362_ = v_a_1340_;
v___y_1363_ = v_a_1341_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1357_, v___y_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_termMapInv_1366_; lean_object* v___x_1367_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_termMapInv_1366_ = lean_ctor_get(v_a_1365_, 4);
lean_inc_ref(v_termMapInv_1366_);
lean_dec(v_a_1365_);
v___x_1367_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1366_, v_e_1330_);
lean_dec_ref(v_termMapInv_1366_);
if (lean_obj_tag(v___x_1367_) == 1)
{
lean_object* v_val_1368_; lean_object* v_fst_1369_; lean_object* v_snd_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v_fst_1369_ = lean_ctor_get(v_val_1368_, 0);
lean_inc_n(v_fst_1369_, 2);
v_snd_1370_ = lean_ctor_get(v_val_1368_, 1);
lean_inc(v_snd_1370_);
lean_dec(v_val_1368_);
v___x_1371_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1372_ = l_Lean_mkApp4(v___x_1371_, v_fst_1369_, v_e_1330_, v_snd_1370_, v_h_1356_);
v___x_1373_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1369_, v___x_1372_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1373_;
}
else
{
lean_object* v___x_1374_; 
lean_dec(v___x_1367_);
v___x_1374_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1330_, v_h_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1374_;
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec_ref(v_h_1356_);
lean_dec_ref(v_e_1330_);
v_a_1375_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1364_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1364_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_h_x3f_1346_);
lean_dec_ref(v_e_1345_);
lean_dec_ref(v_e_1330_);
v_a_1386_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1353_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1353_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec(v_h_x3f_1346_);
lean_dec_ref(v_e_1345_);
lean_dec_ref(v_e_1330_);
lean_dec_ref(v_c_1329_);
v_a_1394_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1347_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1347_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1402_, lean_object* v_e_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1402_, v_e_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec(v_a_1404_);
return v_res_1416_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(0);
v___x_1424_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1425_ = l_Lean_mkConst(v___x_1424_, v___x_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1426_, lean_object* v_e_1427_, lean_object* v_u_1428_, lean_object* v_v_1429_, lean_object* v_k_1430_, lean_object* v_k_x27_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_h_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___x_1472_; 
v___x_1472_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1428_, v_v_1429_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
v___x_1474_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1428_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1476_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref_known(v___x_1474_, 1);
v___x_1476_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1429_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
v___x_1478_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1475_, v_a_1477_, v_k_1430_, v_a_1473_, v_k_x27_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_h_x3f_1479_; 
v_h_x3f_1479_ = lean_ctor_get(v_c_1426_, 4);
lean_inc(v_h_x3f_1479_);
if (lean_obj_tag(v_h_x3f_1479_) == 1)
{
lean_object* v_a_1480_; lean_object* v_e_1481_; lean_object* v_val_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_a_1480_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1478_, 1);
v_e_1481_ = lean_ctor_get(v_c_1426_, 3);
lean_inc_ref(v_e_1481_);
lean_dec_ref(v_c_1426_);
v_val_1482_ = lean_ctor_get(v_h_x3f_1479_, 0);
lean_inc(v_val_1482_);
lean_dec_ref_known(v_h_x3f_1479_, 1);
v___x_1483_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1427_);
v___x_1484_ = l_Lean_mkApp4(v___x_1483_, v_e_1427_, v_e_1481_, v_val_1482_, v_a_1480_);
v_h_1445_ = v___x_1484_;
v___y_1446_ = v_a_1433_;
v___y_1447_ = v_a_1435_;
v___y_1448_ = v_a_1437_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
goto v___jp_1444_;
}
else
{
lean_object* v_a_1485_; 
lean_dec(v_h_x3f_1479_);
lean_dec_ref(v_c_1426_);
v_a_1485_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1485_);
lean_dec_ref_known(v___x_1478_, 1);
v_h_1445_ = v_a_1485_;
v___y_1446_ = v_a_1433_;
v___y_1447_ = v_a_1435_;
v___y_1448_ = v_a_1437_;
v___y_1449_ = v_a_1439_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_c_1426_);
v_a_1486_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1478_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1478_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_a_1475_);
lean_dec(v_a_1473_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_c_1426_);
v_a_1494_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1476_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1476_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_a_1473_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_c_1426_);
v_a_1502_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1474_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1474_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v___x_1507_; 
if (v_isShared_1505_ == 0)
{
v___x_1507_ = v___x_1504_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_a_1502_);
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
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_c_1426_);
v_a_1510_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1472_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1472_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
v___jp_1444_:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1446_, v___y_1451_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v_termMapInv_1455_; lean_object* v___x_1456_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v_termMapInv_1455_ = lean_ctor_get(v_a_1454_, 4);
lean_inc_ref(v_termMapInv_1455_);
lean_dec(v_a_1454_);
v___x_1456_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1455_, v_e_1427_);
lean_dec_ref(v_termMapInv_1455_);
if (lean_obj_tag(v___x_1456_) == 1)
{
lean_object* v_val_1457_; lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_val_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc(v_val_1457_);
lean_dec_ref_known(v___x_1456_, 1);
v_fst_1458_ = lean_ctor_get(v_val_1457_, 0);
lean_inc_n(v_fst_1458_, 2);
v_snd_1459_ = lean_ctor_get(v_val_1457_, 1);
lean_inc(v_snd_1459_);
lean_dec(v_val_1457_);
v___x_1460_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1461_ = l_Lean_mkApp4(v___x_1460_, v_fst_1458_, v_e_1427_, v_snd_1459_, v_h_1445_);
v___x_1462_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1458_, v___x_1461_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1462_;
}
else
{
lean_object* v___x_1463_; 
lean_dec(v___x_1456_);
v___x_1463_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1427_, v_h_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1463_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_h_1445_);
lean_dec_ref(v_e_1427_);
v_a_1464_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1453_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1453_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1518_ = _args[0];
lean_object* v_e_1519_ = _args[1];
lean_object* v_u_1520_ = _args[2];
lean_object* v_v_1521_ = _args[3];
lean_object* v_k_1522_ = _args[4];
lean_object* v_k_x27_1523_ = _args[5];
lean_object* v_a_1524_ = _args[6];
lean_object* v_a_1525_ = _args[7];
lean_object* v_a_1526_ = _args[8];
lean_object* v_a_1527_ = _args[9];
lean_object* v_a_1528_ = _args[10];
lean_object* v_a_1529_ = _args[11];
lean_object* v_a_1530_ = _args[12];
lean_object* v_a_1531_ = _args[13];
lean_object* v_a_1532_ = _args[14];
lean_object* v_a_1533_ = _args[15];
lean_object* v_a_1534_ = _args[16];
lean_object* v_a_1535_ = _args[17];
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1518_, v_e_1519_, v_u_1520_, v_v_1521_, v_k_1522_, v_k_x27_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_k_x27_1523_);
lean_dec_ref(v_k_1522_);
lean_dec(v_v_1521_);
lean_dec(v_u_1520_);
return v_res_1536_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1538_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1539_ = lean_unsigned_to_nat(2u);
v___x_1540_ = lean_unsigned_to_nat(111u);
v___x_1541_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1542_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1543_ = l_mkPanicMessageWithDecl(v___x_1542_, v___x_1541_, v___x_1540_, v___x_1539_, v___x_1538_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1544_, lean_object* v_e_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v_u_1558_; lean_object* v_v_1559_; lean_object* v_e_1560_; lean_object* v_h_x3f_1561_; lean_object* v___x_1562_; 
v_u_1558_ = lean_ctor_get(v_c_1544_, 0);
v_v_1559_ = lean_ctor_get(v_c_1544_, 1);
v_e_1560_ = lean_ctor_get(v_c_1544_, 3);
lean_inc_ref(v_e_1560_);
v_h_x3f_1561_ = lean_ctor_get(v_c_1544_, 4);
lean_inc(v_h_x3f_1561_);
v___x_1562_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1558_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; uint8_t v___x_1564_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc(v_a_1563_);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = lean_nat_dec_eq(v_u_1558_, v_v_1559_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec(v_a_1563_);
lean_dec(v_h_x3f_1561_);
lean_dec_ref(v_e_1560_);
lean_dec_ref(v_e_1545_);
lean_dec_ref(v_c_1544_);
v___x_1565_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1566_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1565_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1566_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1544_);
lean_dec_ref(v_c_1544_);
v___x_1568_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1563_, v___x_1567_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
lean_dec_ref(v___x_1567_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_h_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
if (lean_obj_tag(v_h_x3f_1561_) == 1)
{
lean_object* v_val_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_val_1598_ = lean_ctor_get(v_h_x3f_1561_, 0);
lean_inc(v_val_1598_);
lean_dec_ref_known(v_h_x3f_1561_, 1);
v___x_1599_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1545_);
v___x_1600_ = l_Lean_mkApp4(v___x_1599_, v_e_1545_, v_e_1560_, v_val_1598_, v_a_1569_);
v_h_1571_ = v___x_1600_;
v___y_1572_ = v_a_1547_;
v___y_1573_ = v_a_1549_;
v___y_1574_ = v_a_1551_;
v___y_1575_ = v_a_1553_;
v___y_1576_ = v_a_1554_;
v___y_1577_ = v_a_1555_;
v___y_1578_ = v_a_1556_;
goto v___jp_1570_;
}
else
{
lean_dec(v_h_x3f_1561_);
lean_dec_ref(v_e_1560_);
v_h_1571_ = v_a_1569_;
v___y_1572_ = v_a_1547_;
v___y_1573_ = v_a_1549_;
v___y_1574_ = v_a_1551_;
v___y_1575_ = v_a_1553_;
v___y_1576_ = v_a_1554_;
v___y_1577_ = v_a_1555_;
v___y_1578_ = v_a_1556_;
goto v___jp_1570_;
}
v___jp_1570_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1572_, v___y_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v_termMapInv_1581_; lean_object* v___x_1582_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v_termMapInv_1581_ = lean_ctor_get(v_a_1580_, 4);
lean_inc_ref(v_termMapInv_1581_);
lean_dec(v_a_1580_);
v___x_1582_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1581_, v_e_1545_);
lean_dec_ref(v_termMapInv_1581_);
if (lean_obj_tag(v___x_1582_) == 1)
{
lean_object* v_val_1583_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_val_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v_fst_1584_ = lean_ctor_get(v_val_1583_, 0);
lean_inc_n(v_fst_1584_, 2);
v_snd_1585_ = lean_ctor_get(v_val_1583_, 1);
lean_inc(v_snd_1585_);
lean_dec(v_val_1583_);
v___x_1586_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1587_ = l_Lean_mkApp4(v___x_1586_, v_fst_1584_, v_e_1545_, v_snd_1585_, v_h_1571_);
v___x_1588_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1584_, v___x_1587_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; 
lean_dec(v___x_1582_);
v___x_1589_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1545_, v_h_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_);
return v___x_1589_;
}
}
else
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref(v_h_1571_);
lean_dec_ref(v_e_1545_);
v_a_1590_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1579_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1579_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_h_x3f_1561_);
lean_dec_ref(v_e_1560_);
lean_dec_ref(v_e_1545_);
v_a_1601_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1568_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1568_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_h_x3f_1561_);
lean_dec_ref(v_e_1560_);
lean_dec_ref(v_e_1545_);
lean_dec_ref(v_c_1544_);
v_a_1609_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1562_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1562_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1617_, lean_object* v_e_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1617_, v_e_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec(v_a_1620_);
lean_dec(v_a_1619_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1633_, v_a_1634_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1646_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_termMapInv_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v_termMapInv_1641_ = lean_ctor_get(v_a_1637_, 4);
lean_inc_ref(v_termMapInv_1641_);
lean_dec(v_a_1637_);
v___x_1642_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1641_, v_e_1632_);
lean_dec_ref(v_termMapInv_1641_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1636_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1636_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1655_, v_a_1656_, v_a_1657_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_e_1655_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1660_, v_a_1661_, v_a_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_e_1673_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1686_){
_start:
{
lean_object* v_id_1687_; lean_object* v_type_1688_; lean_object* v_u_1689_; lean_object* v_isPreorderInst_1690_; lean_object* v_leInst_1691_; lean_object* v_ltInst_x3f_1692_; lean_object* v_isPartialInst_x3f_1693_; lean_object* v_isLinearPreInst_x3f_1694_; lean_object* v_lawfulOrderLTInst_x3f_1695_; lean_object* v_ringId_x3f_1696_; uint8_t v_isCommRing_1697_; lean_object* v_ringInst_x3f_1698_; lean_object* v_orderedRingInst_x3f_1699_; lean_object* v_leFn_1700_; lean_object* v_ltFn_x3f_1701_; lean_object* v_nodes_1702_; lean_object* v_nodeMap_1703_; lean_object* v_cnstrs_1704_; lean_object* v_cnstrsOf_1705_; lean_object* v_sources_1706_; lean_object* v_targets_1707_; lean_object* v_proofs_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_id_1687_ = lean_ctor_get(v_s_1686_, 0);
v_type_1688_ = lean_ctor_get(v_s_1686_, 1);
v_u_1689_ = lean_ctor_get(v_s_1686_, 2);
v_isPreorderInst_1690_ = lean_ctor_get(v_s_1686_, 3);
v_leInst_1691_ = lean_ctor_get(v_s_1686_, 4);
v_ltInst_x3f_1692_ = lean_ctor_get(v_s_1686_, 5);
v_isPartialInst_x3f_1693_ = lean_ctor_get(v_s_1686_, 6);
v_isLinearPreInst_x3f_1694_ = lean_ctor_get(v_s_1686_, 7);
v_lawfulOrderLTInst_x3f_1695_ = lean_ctor_get(v_s_1686_, 8);
v_ringId_x3f_1696_ = lean_ctor_get(v_s_1686_, 9);
v_isCommRing_1697_ = lean_ctor_get_uint8(v_s_1686_, sizeof(void*)*22);
v_ringInst_x3f_1698_ = lean_ctor_get(v_s_1686_, 10);
v_orderedRingInst_x3f_1699_ = lean_ctor_get(v_s_1686_, 11);
v_leFn_1700_ = lean_ctor_get(v_s_1686_, 12);
v_ltFn_x3f_1701_ = lean_ctor_get(v_s_1686_, 13);
v_nodes_1702_ = lean_ctor_get(v_s_1686_, 14);
v_nodeMap_1703_ = lean_ctor_get(v_s_1686_, 15);
v_cnstrs_1704_ = lean_ctor_get(v_s_1686_, 16);
v_cnstrsOf_1705_ = lean_ctor_get(v_s_1686_, 17);
v_sources_1706_ = lean_ctor_get(v_s_1686_, 18);
v_targets_1707_ = lean_ctor_get(v_s_1686_, 19);
v_proofs_1708_ = lean_ctor_get(v_s_1686_, 20);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_s_1686_);
if (v_isSharedCheck_1716_ == 0)
{
lean_object* v_unused_1717_; 
v_unused_1717_ = lean_ctor_get(v_s_1686_, 21);
lean_dec(v_unused_1717_);
v___x_1710_ = v_s_1686_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_proofs_1708_);
lean_inc(v_targets_1707_);
lean_inc(v_sources_1706_);
lean_inc(v_cnstrsOf_1705_);
lean_inc(v_cnstrs_1704_);
lean_inc(v_nodeMap_1703_);
lean_inc(v_nodes_1702_);
lean_inc(v_ltFn_x3f_1701_);
lean_inc(v_leFn_1700_);
lean_inc(v_orderedRingInst_x3f_1699_);
lean_inc(v_ringInst_x3f_1698_);
lean_inc(v_ringId_x3f_1696_);
lean_inc(v_lawfulOrderLTInst_x3f_1695_);
lean_inc(v_isLinearPreInst_x3f_1694_);
lean_inc(v_isPartialInst_x3f_1693_);
lean_inc(v_ltInst_x3f_1692_);
lean_inc(v_leInst_1691_);
lean_inc(v_isPreorderInst_1690_);
lean_inc(v_u_1689_);
lean_inc(v_type_1688_);
lean_inc(v_id_1687_);
lean_dec(v_s_1686_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_box(0);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 21, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_id_1687_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_type_1688_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_u_1689_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_isPreorderInst_1690_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_leInst_1691_);
lean_ctor_set(v_reuseFailAlloc_1715_, 5, v_ltInst_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1715_, 6, v_isPartialInst_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1715_, 7, v_isLinearPreInst_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1715_, 8, v_lawfulOrderLTInst_x3f_1695_);
lean_ctor_set(v_reuseFailAlloc_1715_, 9, v_ringId_x3f_1696_);
lean_ctor_set(v_reuseFailAlloc_1715_, 10, v_ringInst_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1715_, 11, v_orderedRingInst_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1715_, 12, v_leFn_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 13, v_ltFn_x3f_1701_);
lean_ctor_set(v_reuseFailAlloc_1715_, 14, v_nodes_1702_);
lean_ctor_set(v_reuseFailAlloc_1715_, 15, v_nodeMap_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 16, v_cnstrs_1704_);
lean_ctor_set(v_reuseFailAlloc_1715_, 17, v_cnstrsOf_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 18, v_sources_1706_);
lean_ctor_set(v_reuseFailAlloc_1715_, 19, v_targets_1707_);
lean_ctor_set(v_reuseFailAlloc_1715_, 20, v_proofs_1708_);
lean_ctor_set(v_reuseFailAlloc_1715_, 21, v___x_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*22, v_isCommRing_1697_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_box(0);
v___x_1725_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1726_ = l_Lean_mkConst(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1727_, lean_object* v_b_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
if (lean_obj_tag(v_as_x27_1727_) == 0)
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1741_, 0, v_b_1728_);
return v___x_1741_;
}
else
{
lean_object* v_head_1742_; lean_object* v_tail_1743_; lean_object* v___x_1744_; 
v_head_1742_ = lean_ctor_get(v_as_x27_1727_, 0);
v_tail_1743_ = lean_ctor_get(v_as_x27_1727_, 1);
v___x_1744_ = lean_box(0);
switch(lean_obj_tag(v_head_1742_))
{
case 0:
{
lean_object* v_c_1745_; lean_object* v_e_1746_; lean_object* v_u_1747_; lean_object* v_v_1748_; lean_object* v_k_1749_; lean_object* v_k_x27_1750_; lean_object* v___x_1751_; 
v_c_1745_ = lean_ctor_get(v_head_1742_, 0);
v_e_1746_ = lean_ctor_get(v_head_1742_, 1);
v_u_1747_ = lean_ctor_get(v_head_1742_, 2);
v_v_1748_ = lean_ctor_get(v_head_1742_, 3);
v_k_1749_ = lean_ctor_get(v_head_1742_, 4);
v_k_x27_1750_ = lean_ctor_get(v_head_1742_, 5);
lean_inc_ref(v_e_1746_);
lean_inc_ref(v_c_1745_);
v___x_1751_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1745_, v_e_1746_, v_u_1747_, v_v_1748_, v_k_1749_, v_k_x27_1750_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref_known(v___x_1751_, 1);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
else
{
return v___x_1751_;
}
}
case 1:
{
lean_object* v_c_1753_; lean_object* v_e_1754_; lean_object* v_u_1755_; lean_object* v_v_1756_; lean_object* v_k_1757_; lean_object* v_k_x27_1758_; lean_object* v___x_1759_; 
v_c_1753_ = lean_ctor_get(v_head_1742_, 0);
v_e_1754_ = lean_ctor_get(v_head_1742_, 1);
v_u_1755_ = lean_ctor_get(v_head_1742_, 2);
v_v_1756_ = lean_ctor_get(v_head_1742_, 3);
v_k_1757_ = lean_ctor_get(v_head_1742_, 4);
v_k_x27_1758_ = lean_ctor_get(v_head_1742_, 5);
lean_inc_ref(v_e_1754_);
lean_inc_ref(v_c_1753_);
v___x_1759_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1753_, v_e_1754_, v_u_1755_, v_v_1756_, v_k_1757_, v_k_x27_1758_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_dec_ref_known(v___x_1759_, 1);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
else
{
return v___x_1759_;
}
}
default: 
{
lean_object* v_u_1761_; lean_object* v_v_1762_; lean_object* v___x_1763_; 
v_u_1761_ = lean_ctor_get(v_head_1742_, 0);
v_v_1762_ = lean_ctor_get(v_head_1742_, 1);
v___x_1763_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1761_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1762_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1900_; lean_object* v___x_1954_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1954_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1764_, v___y_1730_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; uint8_t v___x_1956_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
v___x_1956_ = lean_unbox(v_a_1955_);
lean_dec(v_a_1955_);
if (v___x_1956_ == 0)
{
v___y_1900_ = v___x_1954_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1957_; 
lean_dec_ref_known(v___x_1954_, 1);
v___x_1957_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1766_, v___y_1730_);
v___y_1900_ = v___x_1957_;
goto v___jp_1899_;
}
}
else
{
v___y_1900_ = v___x_1954_;
goto v___jp_1899_;
}
v___jp_1767_:
{
if (lean_obj_tag(v___y_1783_) == 0)
{
lean_object* v_a_1784_; uint8_t v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___y_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___y_1783_, 1);
v___x_1785_ = lean_unbox(v_a_1784_);
lean_dec(v_a_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1774_, v___y_1769_, v___y_1778_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; uint8_t v___x_1789_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___x_1789_ = lean_unbox(v_a_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1761_, v_v_1762_, v___y_1780_, v___y_1778_, v___y_1777_, v___y_1779_, v___y_1770_, v___y_1781_, v___y_1771_, v___y_1775_, v___y_1773_, v___y_1768_, v___y_1772_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1762_, v_u_1761_, v___y_1780_, v___y_1778_, v___y_1777_, v___y_1779_, v___y_1770_, v___y_1781_, v___y_1771_, v___y_1775_, v___y_1773_, v___y_1768_, v___y_1772_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
lean_inc(v_a_1766_);
lean_inc(v_a_1764_);
v___x_1794_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1764_, v_a_1766_, v_a_1791_, v_a_1793_, v___y_1780_, v___y_1778_, v___y_1777_, v___y_1779_, v___y_1770_, v___y_1781_, v___y_1771_, v___y_1775_, v___y_1773_, v___y_1768_, v___y_1772_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1768_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1775_);
lean_inc(v_a_1764_);
v___x_1796_ = lean_infer_type(v_a_1764_, v___y_1775_, v___y_1773_, v___y_1768_, v___y_1772_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = l_Lean_Int_mkType;
v___x_1799_ = lean_expr_eqv(v_a_1797_, v___x_1798_);
lean_dec(v_a_1797_);
if (v___x_1799_ == 0)
{
lean_dec(v_a_1795_);
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; 
v___x_1801_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1769_);
lean_inc_ref(v___y_1774_);
v___x_1802_ = l_Lean_mkApp7(v___x_1801_, v___y_1774_, v___y_1769_, v_a_1764_, v_a_1766_, v___y_1776_, v___y_1782_, v_a_1795_);
v___x_1803_ = lean_unbox(v_a_1788_);
lean_dec(v_a_1788_);
v___x_1804_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1774_, v___y_1769_, v___x_1802_, v___x_1803_, v___y_1778_, v___y_1779_, v___y_1775_, v___y_1773_, v___y_1768_, v___y_1772_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_dec_ref_known(v___x_1804_, 1);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
else
{
return v___x_1804_;
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1795_);
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1806_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1796_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1796_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1814_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1794_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1794_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1791_);
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1822_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1792_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1792_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1830_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1790_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1790_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_dec(v_a_1788_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1839_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1787_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1787_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v___y_1782_);
lean_dec_ref(v___y_1776_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v___y_1769_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1847_ = lean_ctor_get(v___y_1783_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___y_1783_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___y_1783_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___y_1783_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
v___jp_1855_:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1764_, v___y_1857_, v___y_1865_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
if (lean_obj_tag(v_a_1868_) == 1)
{
lean_object* v_val_1869_; lean_object* v_fst_1870_; lean_object* v_snd_1871_; lean_object* v___x_1872_; 
v_val_1869_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v_a_1868_, 1);
v_fst_1870_ = lean_ctor_get(v_val_1869_, 0);
lean_inc(v_fst_1870_);
v_snd_1871_ = lean_ctor_get(v_val_1869_, 1);
lean_inc(v_snd_1871_);
lean_dec(v_val_1869_);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1766_, v___y_1857_, v___y_1865_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
if (lean_obj_tag(v_a_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; lean_object* v___x_1877_; 
v_val_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_a_1873_, 1);
v_fst_1875_ = lean_ctor_get(v_val_1874_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_val_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_val_1874_);
v___x_1877_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1870_, v___y_1857_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
v___y_1768_ = v___y_1865_;
v___y_1769_ = v_fst_1875_;
v___y_1770_ = v___y_1860_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v___y_1866_;
v___y_1773_ = v___y_1864_;
v___y_1774_ = v_fst_1870_;
v___y_1775_ = v___y_1863_;
v___y_1776_ = v_snd_1871_;
v___y_1777_ = v___y_1858_;
v___y_1778_ = v___y_1857_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v___y_1856_;
v___y_1781_ = v___y_1861_;
v___y_1782_ = v_snd_1876_;
v___y_1783_ = v___x_1877_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1880_; 
lean_dec_ref_known(v___x_1877_, 1);
v___x_1880_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1875_, v___y_1857_);
v___y_1768_ = v___y_1865_;
v___y_1769_ = v_fst_1875_;
v___y_1770_ = v___y_1860_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v___y_1866_;
v___y_1773_ = v___y_1864_;
v___y_1774_ = v_fst_1870_;
v___y_1775_ = v___y_1863_;
v___y_1776_ = v_snd_1871_;
v___y_1777_ = v___y_1858_;
v___y_1778_ = v___y_1857_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v___y_1856_;
v___y_1781_ = v___y_1861_;
v___y_1782_ = v_snd_1876_;
v___y_1783_ = v___x_1880_;
goto v___jp_1767_;
}
}
else
{
v___y_1768_ = v___y_1865_;
v___y_1769_ = v_fst_1875_;
v___y_1770_ = v___y_1860_;
v___y_1771_ = v___y_1862_;
v___y_1772_ = v___y_1866_;
v___y_1773_ = v___y_1864_;
v___y_1774_ = v_fst_1870_;
v___y_1775_ = v___y_1863_;
v___y_1776_ = v_snd_1871_;
v___y_1777_ = v___y_1858_;
v___y_1778_ = v___y_1857_;
v___y_1779_ = v___y_1859_;
v___y_1780_ = v___y_1856_;
v___y_1781_ = v___y_1861_;
v___y_1782_ = v_snd_1876_;
v___y_1783_ = v___x_1877_;
goto v___jp_1767_;
}
}
else
{
lean_dec(v_a_1873_);
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
lean_dec(v_snd_1871_);
lean_dec(v_fst_1870_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1882_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1872_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1872_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_dec(v_a_1868_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_as_x27_1727_ = v_tail_1743_;
v_b_1728_ = v___x_1744_;
goto _start;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1891_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1867_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1867_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
v___jp_1899_:
{
if (lean_obj_tag(v___y_1900_) == 0)
{
lean_object* v_a_1901_; uint8_t v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___y_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___y_1900_, 1);
v___x_1902_ = lean_unbox(v_a_1901_);
lean_dec(v_a_1901_);
if (v___x_1902_ == 0)
{
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
v___y_1865_ = v___y_1738_;
v___y_1866_ = v___y_1739_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1764_, v_a_1766_, v___y_1730_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; uint8_t v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = lean_unbox(v_a_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1761_, v_v_1762_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1762_, v_u_1761_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
lean_inc(v_a_1766_);
lean_inc(v_a_1764_);
v___x_1910_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1764_, v_a_1766_, v_a_1907_, v_a_1909_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = lean_unbox(v_a_1904_);
lean_dec(v_a_1904_);
lean_inc(v_a_1766_);
lean_inc(v_a_1764_);
v___x_1913_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1764_, v_a_1766_, v_a_1911_, v___x_1912_, v___y_1730_, v___y_1732_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_dec_ref_known(v___x_1913_, 1);
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
v___y_1865_ = v___y_1738_;
v___y_1866_ = v___y_1739_;
goto v___jp_1855_;
}
else
{
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
return v___x_1913_;
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1904_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1914_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1910_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1907_);
lean_dec(v_a_1904_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1922_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1908_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1908_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1904_);
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1930_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1906_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1906_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
else
{
lean_dec(v_a_1904_);
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
v___y_1859_ = v___y_1732_;
v___y_1860_ = v___y_1733_;
v___y_1861_ = v___y_1734_;
v___y_1862_ = v___y_1735_;
v___y_1863_ = v___y_1736_;
v___y_1864_ = v___y_1737_;
v___y_1865_ = v___y_1738_;
v___y_1866_ = v___y_1739_;
goto v___jp_1855_;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1938_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1903_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1903_);
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
lean_dec(v_a_1766_);
lean_dec(v_a_1764_);
v_a_1946_ = lean_ctor_get(v___y_1900_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___y_1900_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___y_1900_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___y_1900_);
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
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
lean_dec(v_a_1764_);
v_a_1958_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1765_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1765_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1763_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1763_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1974_, lean_object* v_b_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1974_, v_b_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec(v_as_x27_1974_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Meta_Grind_Order_getStruct(v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___f_2004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_2005_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_2004_, v_a_1990_, v_a_1991_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_propagate_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec_ref_known(v___x_2005_, 1);
v_propagate_2006_ = lean_ctor_get(v_a_2003_, 21);
lean_inc(v_propagate_2006_);
lean_dec(v_a_2003_);
v___x_2007_ = lean_box(0);
v___x_2008_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_2006_, v___x_2007_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_propagate_2006_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v___x_2008_, 0);
lean_dec(v_unused_2016_);
v___x_2010_ = v___x_2008_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_dec(v___x_2008_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2007_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2007_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
else
{
return v___x_2008_;
}
}
else
{
lean_dec(v_a_2003_);
return v___x_2005_;
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
v_a_2017_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2002_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2002_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec(v_a_2025_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2038_, lean_object* v_as_x27_2039_, lean_object* v_b_2040_, lean_object* v_a_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2039_, v_b_2040_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2055_, lean_object* v_as_x27_2056_, lean_object* v_b_2057_, lean_object* v_a_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2055_, v_as_x27_2056_, v_b_2057_, v_a_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec(v_as_x27_2056_);
lean_dec(v_as_2055_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2073_, v_a_2077_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v_termMapInv_2082_; lean_object* v___x_2083_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2080_, 1);
v_termMapInv_2082_ = lean_ctor_get(v_a_2081_, 4);
lean_inc_ref(v_termMapInv_2082_);
lean_dec(v_a_2081_);
v___x_2083_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2082_, v_e_2072_);
lean_dec_ref(v_termMapInv_2082_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v_fst_2085_; lean_object* v___x_2086_; 
lean_dec_ref(v_e_2072_);
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v_fst_2085_ = lean_ctor_get(v_val_2084_, 0);
lean_inc(v_fst_2085_);
lean_dec(v_val_2084_);
v___x_2086_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2085_, v_a_2073_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; uint8_t v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
v___x_2088_ = lean_unbox(v_a_2087_);
lean_dec(v_a_2087_);
if (v___x_2088_ == 0)
{
lean_dec(v_fst_2085_);
return v___x_2086_;
}
else
{
lean_object* v___x_2089_; 
lean_dec_ref_known(v___x_2086_, 1);
v___x_2089_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2085_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2089_;
}
}
else
{
lean_dec(v_fst_2085_);
return v___x_2086_;
}
}
else
{
lean_object* v___x_2090_; 
lean_dec(v___x_2083_);
v___x_2090_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2072_, v_a_2073_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
v___x_2092_ = lean_unbox(v_a_2091_);
lean_dec(v_a_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v_e_2072_);
return v___x_2090_;
}
else
{
lean_object* v___x_2093_; 
lean_dec_ref_known(v___x_2090_, 1);
v___x_2093_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_);
return v___x_2093_;
}
}
else
{
lean_dec_ref(v_e_2072_);
return v___x_2090_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v_e_2072_);
v_a_2094_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2080_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2080_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2111_, v_a_2113_, v_a_2117_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec(v_a_2126_);
return v_res_2138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2147_ = l_Lean_Name_append(v___x_2146_, v___x_2145_);
return v___x_2147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2150_ = l_Lean_stringToMessageData(v___x_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2152_, lean_object* v_v_2153_, lean_object* v_k_2154_, lean_object* v_c_2155_, lean_object* v_e_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v___x_2169_; 
lean_inc_ref(v_e_2156_);
v___x_2169_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2156_, v_a_2158_, v_a_2162_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2269_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2269_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2269_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_unbox(v_a_2170_);
lean_dec(v_a_2170_);
if (v___x_2174_ == 0)
{
lean_object* v_toCold_2175_; lean_object* v_options_2176_; lean_object* v_inheritedTraceOptions_2177_; uint8_t v_hasTrace_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; 
v_toCold_2175_ = lean_ctor_get(v_a_2166_, 0);
v_options_2176_ = lean_ctor_get(v_toCold_2175_, 2);
v_inheritedTraceOptions_2177_ = lean_ctor_get(v_toCold_2175_, 11);
v_hasTrace_2178_ = lean_ctor_get_uint8(v_options_2176_, sizeof(void*)*1);
v___x_2179_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2155_);
v___x_2180_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2154_, v___x_2179_);
if (v_hasTrace_2178_ == 0)
{
v___y_2182_ = v_a_2157_;
v___y_2183_ = v_a_2158_;
v___y_2184_ = v_a_2159_;
v___y_2185_ = v_a_2160_;
v___y_2186_ = v_a_2161_;
v___y_2187_ = v_a_2162_;
v___y_2188_ = v_a_2163_;
v___y_2189_ = v_a_2164_;
v___y_2190_ = v_a_2165_;
v___y_2191_ = v_a_2166_;
v___y_2192_ = v_a_2167_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2177_, v_options_2176_, v___x_2200_);
if (v___x_2201_ == 0)
{
v___y_2182_ = v_a_2157_;
v___y_2183_ = v_a_2158_;
v___y_2184_ = v_a_2159_;
v___y_2185_ = v_a_2160_;
v___y_2186_ = v_a_2161_;
v___y_2187_ = v_a_2162_;
v___y_2188_ = v_a_2163_;
v___y_2189_ = v_a_2164_;
v___y_2190_ = v_a_2165_;
v___y_2191_ = v_a_2166_;
v___y_2192_ = v_a_2167_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2152_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2153_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2206_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
v___x_2206_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2155_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v_k_2208_; uint8_t v_strict_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___y_2226_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v_k_2208_ = lean_ctor_get(v_k_2154_, 0);
v_strict_2209_ = lean_ctor_get_uint8(v_k_2154_, sizeof(void*)*1);
v___x_2210_ = l_Lean_MessageData_ofExpr(v_a_2203_);
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2210_);
lean_ctor_set(v___x_2221_, 1, v___x_2211_);
v___x_2222_ = l_Lean_MessageData_ofExpr(v_a_2205_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2221_);
lean_ctor_set(v___x_2223_, 1, v___x_2222_);
v___x_2224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
lean_ctor_set(v___x_2224_, 1, v___x_2211_);
if (v_strict_2209_ == 0)
{
lean_object* v___x_2237_; 
v___x_2237_ = l_Int_repr(v_k_2208_);
v___y_2226_ = v___x_2237_;
goto v___jp_2225_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = l_Int_repr(v_k_2208_);
v___x_2239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2240_ = lean_string_append(v___x_2238_, v___x_2239_);
v___y_2226_ = v___x_2240_;
goto v___jp_2225_;
}
v___jp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2215_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___y_2214_);
v___x_2216_ = l_Lean_MessageData_ofFormat(v___x_2215_);
v___x_2217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___y_2213_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
lean_ctor_set(v___x_2218_, 1, v___x_2211_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_a_2207_);
v___x_2220_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2199_, v___x_2219_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_dec_ref_known(v___x_2220_, 1);
v___y_2182_ = v_a_2157_;
v___y_2183_ = v_a_2158_;
v___y_2184_ = v_a_2159_;
v___y_2185_ = v_a_2160_;
v___y_2186_ = v_a_2161_;
v___y_2187_ = v_a_2162_;
v___y_2188_ = v_a_2163_;
v___y_2189_ = v_a_2164_;
v___y_2190_ = v_a_2165_;
v___y_2191_ = v_a_2166_;
v___y_2192_ = v_a_2167_;
goto v___jp_2181_;
}
else
{
lean_dec_ref(v___x_2179_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
return v___x_2220_;
}
}
v___jp_2225_:
{
lean_object* v_k_2227_; uint8_t v_strict_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_k_2227_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_k_2227_);
v_strict_2228_ = lean_ctor_get_uint8(v___x_2179_, sizeof(void*)*1);
v___x_2229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___y_2226_);
v___x_2230_ = l_Lean_MessageData_ofFormat(v___x_2229_);
v___x_2231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2224_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2211_);
if (v_strict_2228_ == 0)
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Int_repr(v_k_2227_);
lean_dec(v_k_2227_);
v___y_2213_ = v___x_2232_;
v___y_2214_ = v___x_2233_;
goto v___jp_2212_;
}
else
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2234_ = l_Int_repr(v_k_2227_);
lean_dec(v_k_2227_);
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2236_ = lean_string_append(v___x_2234_, v___x_2235_);
v___y_2213_ = v___x_2232_;
v___y_2214_ = v___x_2236_;
goto v___jp_2212_;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec(v_a_2205_);
lean_dec(v_a_2203_);
lean_dec_ref(v___x_2179_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v_a_2241_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2206_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2206_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2203_);
lean_dec_ref(v___x_2179_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v_a_2249_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2204_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2204_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v___x_2179_);
lean_del_object(v___x_2172_);
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v_a_2257_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2202_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2202_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
v___jp_2181_:
{
if (v___x_2180_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec_ref(v___x_2179_);
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v___x_2193_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2193_);
v___x_2195_ = v___x_2172_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_del_object(v___x_2172_);
v___x_2197_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2197_, 0, v_c_2155_);
lean_ctor_set(v___x_2197_, 1, v_e_2156_);
lean_ctor_set(v___x_2197_, 2, v_u_2152_);
lean_ctor_set(v___x_2197_, 3, v_v_2153_);
lean_ctor_set(v___x_2197_, 4, v_k_2154_);
lean_ctor_set(v___x_2197_, 5, v___x_2179_);
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2197_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2198_;
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v___x_2265_ = lean_box(0);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2265_);
v___x_2267_ = v___x_2172_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_e_2156_);
lean_dec_ref(v_c_2155_);
lean_dec_ref(v_k_2154_);
lean_dec(v_v_2153_);
lean_dec(v_u_2152_);
v_a_2270_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2169_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2169_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2278_ = _args[0];
lean_object* v_v_2279_ = _args[1];
lean_object* v_k_2280_ = _args[2];
lean_object* v_c_2281_ = _args[3];
lean_object* v_e_2282_ = _args[4];
lean_object* v_a_2283_ = _args[5];
lean_object* v_a_2284_ = _args[6];
lean_object* v_a_2285_ = _args[7];
lean_object* v_a_2286_ = _args[8];
lean_object* v_a_2287_ = _args[9];
lean_object* v_a_2288_ = _args[10];
lean_object* v_a_2289_ = _args[11];
lean_object* v_a_2290_ = _args[12];
lean_object* v_a_2291_ = _args[13];
lean_object* v_a_2292_ = _args[14];
lean_object* v_a_2293_ = _args[15];
lean_object* v_a_2294_ = _args[16];
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2278_, v_v_2279_, v_k_2280_, v_c_2281_, v_e_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec(v_a_2283_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2297_, v_a_2301_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_termMapInv_2306_; lean_object* v___x_2307_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_termMapInv_2306_ = lean_ctor_get(v_a_2305_, 4);
lean_inc_ref(v_termMapInv_2306_);
lean_dec(v_a_2305_);
v___x_2307_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2306_, v_e_2296_);
lean_dec_ref(v_termMapInv_2306_);
if (lean_obj_tag(v___x_2307_) == 1)
{
lean_object* v_val_2308_; lean_object* v_fst_2309_; lean_object* v___x_2310_; 
lean_dec_ref(v_e_2296_);
v_val_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_val_2308_);
lean_dec_ref_known(v___x_2307_, 1);
v_fst_2309_ = lean_ctor_get(v_val_2308_, 0);
lean_inc(v_fst_2309_);
lean_dec(v_val_2308_);
v___x_2310_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2309_, v_a_2297_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; uint8_t v___x_2312_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
v___x_2312_ = lean_unbox(v_a_2311_);
lean_dec(v_a_2311_);
if (v___x_2312_ == 0)
{
lean_dec(v_fst_2309_);
return v___x_2310_;
}
else
{
lean_object* v___x_2313_; 
lean_dec_ref_known(v___x_2310_, 1);
v___x_2313_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2309_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2313_;
}
}
else
{
lean_dec(v_fst_2309_);
return v___x_2310_;
}
}
else
{
lean_object* v___x_2314_; 
lean_dec(v___x_2307_);
v___x_2314_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2296_, v_a_2297_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
v___x_2316_ = lean_unbox(v_a_2315_);
lean_dec(v_a_2315_);
if (v___x_2316_ == 0)
{
lean_dec_ref(v_e_2296_);
return v___x_2314_;
}
else
{
lean_object* v___x_2317_; 
lean_dec_ref_known(v___x_2314_, 1);
v___x_2317_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2317_;
}
}
else
{
lean_dec_ref(v_e_2296_);
return v___x_2314_;
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v_e_2296_);
v_a_2318_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2304_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2304_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2335_, v_a_2337_, v_a_2341_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec(v_a_2350_);
return v_res_2362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2371_ = l_Lean_Name_append(v___x_2370_, v___x_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2375_, lean_object* v_v_2376_, lean_object* v_k_2377_, lean_object* v_c_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v___x_2392_; 
lean_inc_ref(v_e_2379_);
v___x_2392_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2379_, v_a_2381_, v_a_2385_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2494_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2395_ = v___x_2392_;
v_isShared_2396_ = v_isSharedCheck_2494_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2494_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_unbox(v_a_2393_);
lean_dec(v_a_2393_);
if (v___x_2397_ == 0)
{
lean_object* v_toCold_2398_; lean_object* v_options_2399_; lean_object* v_inheritedTraceOptions_2400_; uint8_t v_hasTrace_2401_; lean_object* v___x_2402_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; 
v_toCold_2398_ = lean_ctor_get(v_a_2389_, 0);
v_options_2399_ = lean_ctor_get(v_toCold_2398_, 2);
v_inheritedTraceOptions_2400_ = lean_ctor_get(v_toCold_2398_, 11);
v_hasTrace_2401_ = lean_ctor_get_uint8(v_options_2399_, sizeof(void*)*1);
v___x_2402_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2378_);
if (v_hasTrace_2401_ == 0)
{
v___y_2404_ = v_a_2380_;
v___y_2405_ = v_a_2381_;
v___y_2406_ = v_a_2382_;
v___y_2407_ = v_a_2383_;
v___y_2408_ = v_a_2384_;
v___y_2409_ = v_a_2385_;
v___y_2410_ = v_a_2386_;
v___y_2411_ = v_a_2387_;
v___y_2412_ = v_a_2388_;
v___y_2413_ = v_a_2389_;
v___y_2414_ = v_a_2390_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2400_, v_options_2399_, v___x_2424_);
if (v___x_2425_ == 0)
{
v___y_2404_ = v_a_2380_;
v___y_2405_ = v_a_2381_;
v___y_2406_ = v_a_2382_;
v___y_2407_ = v_a_2383_;
v___y_2408_ = v_a_2384_;
v___y_2409_ = v_a_2385_;
v___y_2410_ = v_a_2386_;
v___y_2411_ = v_a_2387_;
v___y_2412_ = v_a_2388_;
v___y_2413_ = v_a_2389_;
v___y_2414_ = v_a_2390_;
goto v___jp_2403_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2375_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v___x_2428_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2376_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2378_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v_k_2442_; uint8_t v_strict_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___y_2451_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref_known(v___x_2430_, 1);
v_k_2442_ = lean_ctor_get(v_k_2377_, 0);
v_strict_2443_ = lean_ctor_get_uint8(v_k_2377_, sizeof(void*)*1);
v___x_2444_ = l_Lean_MessageData_ofExpr(v_a_2427_);
v___x_2445_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2444_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = l_Lean_MessageData_ofExpr(v_a_2429_);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
lean_ctor_set(v___x_2449_, 1, v___x_2445_);
if (v_strict_2443_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Int_repr(v_k_2442_);
v___y_2451_ = v___x_2462_;
goto v___jp_2450_;
}
else
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2463_ = l_Int_repr(v_k_2442_);
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2465_ = lean_string_append(v___x_2463_, v___x_2464_);
v___y_2451_ = v___x_2465_;
goto v___jp_2450_;
}
v___jp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2435_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___y_2434_);
v___x_2436_ = l_Lean_MessageData_ofFormat(v___x_2435_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___y_2433_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v_a_2431_);
v___x_2441_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2423_, v___x_2440_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_dec_ref_known(v___x_2441_, 1);
v___y_2404_ = v_a_2380_;
v___y_2405_ = v_a_2381_;
v___y_2406_ = v_a_2382_;
v___y_2407_ = v_a_2383_;
v___y_2408_ = v_a_2384_;
v___y_2409_ = v_a_2385_;
v___y_2410_ = v_a_2386_;
v___y_2411_ = v_a_2387_;
v___y_2412_ = v_a_2388_;
v___y_2413_ = v_a_2389_;
v___y_2414_ = v_a_2390_;
goto v___jp_2403_;
}
else
{
lean_dec_ref(v___x_2402_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
return v___x_2441_;
}
}
v___jp_2450_:
{
lean_object* v_k_2452_; uint8_t v_strict_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v_k_2452_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_k_2452_);
v_strict_2453_ = lean_ctor_get_uint8(v___x_2402_, sizeof(void*)*1);
v___x_2454_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2454_, 0, v___y_2451_);
v___x_2455_ = l_Lean_MessageData_ofFormat(v___x_2454_);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2449_);
lean_ctor_set(v___x_2456_, 1, v___x_2455_);
v___x_2457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
lean_ctor_set(v___x_2457_, 1, v___x_2445_);
if (v_strict_2453_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Int_repr(v_k_2452_);
lean_dec(v_k_2452_);
v___y_2433_ = v___x_2457_;
v___y_2434_ = v___x_2458_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = l_Int_repr(v_k_2452_);
lean_dec(v_k_2452_);
v___x_2460_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2461_ = lean_string_append(v___x_2459_, v___x_2460_);
v___y_2433_ = v___x_2457_;
v___y_2434_ = v___x_2461_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec(v_a_2429_);
lean_dec(v_a_2427_);
lean_dec_ref(v___x_2402_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v_a_2466_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2430_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2430_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2427_);
lean_dec_ref(v___x_2402_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v_a_2474_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2428_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2428_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
lean_dec_ref(v___x_2402_);
lean_del_object(v___x_2395_);
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v_a_2482_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2484_ = v___x_2426_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_a_2482_);
lean_dec(v___x_2426_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2482_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
v___jp_2403_:
{
lean_object* v___x_2415_; uint8_t v___x_2416_; 
lean_inc_ref(v___x_2402_);
v___x_2415_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2377_, v___x_2402_);
v___x_2416_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2415_);
lean_dec_ref(v___x_2415_);
if (v___x_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_dec_ref(v___x_2402_);
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v___x_2417_ = lean_box(0);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2417_);
v___x_2419_ = v___x_2395_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_del_object(v___x_2395_);
v___x_2421_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2421_, 0, v_c_2378_);
lean_ctor_set(v___x_2421_, 1, v_e_2379_);
lean_ctor_set(v___x_2421_, 2, v_u_2375_);
lean_ctor_set(v___x_2421_, 3, v_v_2376_);
lean_ctor_set(v___x_2421_, 4, v_k_2377_);
lean_ctor_set(v___x_2421_, 5, v___x_2402_);
v___x_2422_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2421_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
return v___x_2422_;
}
}
}
else
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v___x_2490_ = lean_box(0);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2490_);
v___x_2492_ = v___x_2395_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v_e_2379_);
lean_dec_ref(v_c_2378_);
lean_dec_ref(v_k_2377_);
lean_dec(v_v_2376_);
lean_dec(v_u_2375_);
v_a_2495_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2392_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2392_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2503_ = _args[0];
lean_object* v_v_2504_ = _args[1];
lean_object* v_k_2505_ = _args[2];
lean_object* v_c_2506_ = _args[3];
lean_object* v_e_2507_ = _args[4];
lean_object* v_a_2508_ = _args[5];
lean_object* v_a_2509_ = _args[6];
lean_object* v_a_2510_ = _args[7];
lean_object* v_a_2511_ = _args[8];
lean_object* v_a_2512_ = _args[9];
lean_object* v_a_2513_ = _args[10];
lean_object* v_a_2514_ = _args[11];
lean_object* v_a_2515_ = _args[12];
lean_object* v_a_2516_ = _args[13];
lean_object* v_a_2517_ = _args[14];
lean_object* v_a_2518_ = _args[15];
lean_object* v_a_2519_ = _args[16];
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2503_, v_v_2504_, v_k_2505_, v_c_2506_, v_e_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
lean_dec(v_a_2514_);
lean_dec_ref(v_a_2513_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec(v_a_2509_);
lean_dec(v_a_2508_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2521_, lean_object* v_x_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_fst_2535_; lean_object* v_snd_2536_; lean_object* v___x_2537_; 
v_fst_2535_ = lean_ctor_get(v_x_2522_, 0);
lean_inc(v_fst_2535_);
v_snd_2536_ = lean_ctor_get(v_x_2522_, 1);
lean_inc(v_snd_2536_);
lean_dec_ref(v_x_2522_);
lean_inc(v___y_2533_);
lean_inc_ref(v___y_2532_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc_ref(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc(v___y_2524_);
lean_inc(v___y_2523_);
v___x_2537_ = lean_apply_14(v_f_2521_, v_fst_2535_, v_snd_2536_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, lean_box(0));
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2538_, lean_object* v_x_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2538_, v_x_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec(v___y_2541_);
lean_dec(v___y_2540_);
return v_res_2552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___f_2557_; 
v___x_2556_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2557_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2557_, 0, v___x_2556_);
return v___f_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2558_; lean_object* v___f_2559_; 
v___f_2558_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2559_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2559_, 0, v___f_2558_);
lean_closure_set(v___f_2559_, 1, v___f_2558_);
return v___f_2559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2560_, lean_object* v_v_2561_, lean_object* v_f_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v___x_2575_; lean_object* v_toApplicative_2576_; lean_object* v_toFunctor_2577_; lean_object* v_toSeq_2578_; lean_object* v_toSeqLeft_2579_; lean_object* v_toSeqRight_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v_toApplicative_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2653_; 
v___x_2575_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2576_ = lean_ctor_get(v___x_2575_, 0);
v_toFunctor_2577_ = lean_ctor_get(v_toApplicative_2576_, 0);
v_toSeq_2578_ = lean_ctor_get(v_toApplicative_2576_, 2);
v_toSeqLeft_2579_ = lean_ctor_get(v_toApplicative_2576_, 3);
v_toSeqRight_2580_ = lean_ctor_get(v_toApplicative_2576_, 4);
v___f_2581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2577_, 2);
v___f_2583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2583_, 0, v_toFunctor_2577_);
v___f_2584_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2584_, 0, v_toFunctor_2577_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___f_2583_);
lean_ctor_set(v___x_2585_, 1, v___f_2584_);
lean_inc(v_toSeqRight_2580_);
v___f_2586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2586_, 0, v_toSeqRight_2580_);
lean_inc(v_toSeqLeft_2579_);
v___f_2587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2587_, 0, v_toSeqLeft_2579_);
lean_inc(v_toSeq_2578_);
v___f_2588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2588_, 0, v_toSeq_2578_);
v___x_2589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2585_);
lean_ctor_set(v___x_2589_, 1, v___f_2581_);
lean_ctor_set(v___x_2589_, 2, v___f_2588_);
lean_ctor_set(v___x_2589_, 3, v___f_2587_);
lean_ctor_set(v___x_2589_, 4, v___f_2586_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v___f_2582_);
v___x_2591_ = l_StateRefT_x27_instMonad___redArg(v___x_2590_);
v_toApplicative_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___x_2591_, 1);
lean_dec(v_unused_2654_);
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2653_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_toApplicative_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2653_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_toFunctor_2596_; lean_object* v_toSeq_2597_; lean_object* v_toSeqLeft_2598_; lean_object* v_toSeqRight_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2651_; 
v_toFunctor_2596_ = lean_ctor_get(v_toApplicative_2592_, 0);
v_toSeq_2597_ = lean_ctor_get(v_toApplicative_2592_, 2);
v_toSeqLeft_2598_ = lean_ctor_get(v_toApplicative_2592_, 3);
v_toSeqRight_2599_ = lean_ctor_get(v_toApplicative_2592_, 4);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_toApplicative_2592_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v_toApplicative_2592_, 1);
lean_dec(v_unused_2652_);
v___x_2601_ = v_toApplicative_2592_;
v_isShared_2602_ = v_isSharedCheck_2651_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_toSeqRight_2599_);
lean_inc(v_toSeqLeft_2598_);
lean_inc(v_toSeq_2597_);
lean_inc(v_toFunctor_2596_);
lean_dec(v_toApplicative_2592_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2651_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___x_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___x_2612_; 
v___f_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2596_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toFunctor_2596_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toFunctor_2596_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___f_2605_);
lean_ctor_set(v___x_2607_, 1, v___f_2606_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeqRight_2599_);
v___f_2609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2609_, 0, v_toSeqLeft_2598_);
v___f_2610_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2610_, 0, v_toSeq_2597_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 4, v___f_2608_);
lean_ctor_set(v___x_2601_, 3, v___f_2609_);
lean_ctor_set(v___x_2601_, 2, v___f_2610_);
lean_ctor_set(v___x_2601_, 1, v___f_2603_);
lean_ctor_set(v___x_2601_, 0, v___x_2607_);
v___x_2612_ = v___x_2601_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2607_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___f_2603_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v___f_2610_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v___f_2609_);
lean_ctor_set(v_reuseFailAlloc_2650_, 4, v___f_2608_);
v___x_2612_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
lean_object* v___x_2614_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v___f_2604_);
lean_ctor_set(v___x_2594_, 0, v___x_2612_);
v___x_2614_ = v___x_2594_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2612_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___f_2604_);
v___x_2614_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; 
v___x_2615_ = l_StateRefT_x27_instMonad___redArg(v___x_2614_);
v___x_2616_ = l_ReaderT_instMonad___redArg(v___x_2615_);
v___x_2617_ = l_StateRefT_x27_instMonad___redArg(v___x_2616_);
v___x_2618_ = l_ReaderT_instMonad___redArg(v___x_2617_);
v___x_2619_ = l_ReaderT_instMonad___redArg(v___x_2618_);
v___x_2620_ = l_StateRefT_x27_instMonad___redArg(v___x_2619_);
v___x_2621_ = l_ReaderT_instMonad___redArg(v___x_2620_);
v___f_2622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2623_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2640_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2640_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___f_2628_; lean_object* v_cnstrsOf_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___f_2628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2629_ = lean_ctor_get(v_a_2624_, 17);
lean_inc_ref(v_cnstrsOf_2629_);
lean_dec(v_a_2624_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_u_2560_);
lean_ctor_set(v___x_2630_, 1, v_v_2561_);
v___x_2631_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2628_, v___f_2622_, v_cnstrsOf_2629_, v___x_2630_);
lean_dec_ref(v_cnstrsOf_2629_);
if (lean_obj_tag(v___x_2631_) == 1)
{
lean_object* v_val_2632_; lean_object* v___f_2633_; lean_object* v___x_1457__overap_2634_; lean_object* v___x_2635_; 
lean_del_object(v___x_2626_);
v_val_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___f_2633_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2633_, 0, v_f_2562_);
v___x_1457__overap_2634_ = l_List_forM___redArg(v___x_2621_, v_val_2632_, v___f_2633_);
lean_inc(v_a_2573_);
lean_inc_ref(v_a_2572_);
lean_inc(v_a_2571_);
lean_inc_ref(v_a_2570_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc_ref(v_a_2566_);
lean_inc(v_a_2565_);
lean_inc(v_a_2564_);
lean_inc(v_a_2563_);
v___x_2635_ = lean_apply_12(v___x_1457__overap_2634_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, lean_box(0));
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_dec(v___x_2631_);
lean_dec_ref(v___x_2621_);
lean_dec_ref(v_f_2562_);
v___x_2636_ = lean_box(0);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2636_);
v___x_2638_ = v___x_2626_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v___x_2621_);
lean_dec_ref(v_f_2562_);
lean_dec(v_v_2561_);
lean_dec(v_u_2560_);
v_a_2641_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2623_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2623_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2655_, lean_object* v_v_2656_, lean_object* v_f_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2655_, v_v_2656_, v_f_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
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
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2672_, v_a_2673_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2698_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2698_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2698_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v_termMapInv_2680_; lean_object* v___x_2681_; 
v_termMapInv_2680_ = lean_ctor_get(v_a_2676_, 4);
lean_inc_ref(v_termMapInv_2680_);
lean_dec(v_a_2676_);
v___x_2681_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2680_, v_e_2671_);
lean_dec_ref(v_termMapInv_2680_);
if (lean_obj_tag(v___x_2681_) == 1)
{
lean_object* v_val_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2693_; 
v_val_2682_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2684_ = v___x_2681_;
v_isShared_2685_ = v_isSharedCheck_2693_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_val_2682_);
lean_dec(v___x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2693_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v_fst_2686_; lean_object* v___x_2688_; 
v_fst_2686_ = lean_ctor_get(v_val_2682_, 0);
lean_inc(v_fst_2686_);
lean_dec(v_val_2682_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v_fst_2686_);
v___x_2688_ = v___x_2684_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_fst_2686_);
v___x_2688_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2690_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2688_);
v___x_2690_ = v___x_2678_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
lean_dec(v___x_2681_);
v___x_2694_ = lean_box(0);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 0, v___x_2694_);
v___x_2696_ = v___x_2678_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_a_2699_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2675_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2675_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2707_, v_a_2708_, v_a_2709_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_e_2707_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2712_, v_a_2713_, v_a_2721_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec_ref(v_a_2728_);
lean_dec(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2725_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2738_, lean_object* v_v_2739_, lean_object* v_k_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; uint8_t v___x_2796_; 
v___x_2796_ = lean_nat_dec_eq(v_u_2738_, v_v_2739_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2935_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2935_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2935_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_unbox(v_a_2798_);
lean_dec(v_a_2798_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2803_ = lean_box(0);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2803_);
v___x_2805_ = v___x_2800_;
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
else
{
uint8_t v___x_2807_; 
v___x_2807_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2740_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2808_ = lean_box(0);
if (v_isShared_2801_ == 0)
{
lean_ctor_set(v___x_2800_, 0, v___x_2808_);
v___x_2810_ = v___x_2800_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
else
{
lean_object* v___x_2812_; 
lean_del_object(v___x_2800_);
v___x_2812_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_2739_, v_u_2738_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2926_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2926_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2926_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
if (lean_obj_tag(v_a_2813_) == 1)
{
lean_object* v_val_2817_; uint8_t v___x_2818_; 
v_val_2817_ = lean_ctor_get(v_a_2813_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v_a_2813_, 1);
v___x_2818_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2817_);
lean_dec(v_val_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2819_ = lean_box(0);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2819_);
v___x_2821_ = v___x_2815_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
else
{
lean_object* v___x_2823_; 
lean_del_object(v___x_2815_);
v___x_2823_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2738_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2739_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___y_2828_; lean_object* v___x_2902_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref_known(v___x_2825_, 1);
v___x_2902_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2824_, v_a_2742_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; uint8_t v___x_2904_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_a_2903_);
v___x_2904_ = lean_unbox(v_a_2903_);
lean_dec(v_a_2903_);
if (v___x_2904_ == 0)
{
v___y_2828_ = v___x_2902_;
goto v___jp_2827_;
}
else
{
lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2902_, 1);
v___x_2905_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2826_, v_a_2742_);
v___y_2828_ = v___x_2905_;
goto v___jp_2827_;
}
}
else
{
v___y_2828_ = v___x_2902_;
goto v___jp_2827_;
}
v___jp_2827_:
{
if (lean_obj_tag(v___y_2828_) == 0)
{
lean_object* v_a_2829_; uint8_t v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___y_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___y_2828_, 1);
v___x_2830_ = lean_unbox(v_a_2829_);
lean_dec(v_a_2829_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2824_, v_a_2742_, v_a_2750_);
lean_dec(v_a_2824_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2864_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2864_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2864_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_val_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2834_);
v_val_2836_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2836_);
lean_dec_ref_known(v_a_2832_, 1);
v___x_2837_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2826_, v_a_2742_, v_a_2750_);
lean_dec(v_a_2826_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2851_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2851_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2851_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
if (lean_obj_tag(v_a_2838_) == 1)
{
lean_object* v_val_2842_; lean_object* v___x_2843_; 
lean_del_object(v___x_2840_);
v_val_2842_ = lean_ctor_get(v_a_2838_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_a_2838_, 1);
v___x_2843_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2836_, v_a_2742_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; uint8_t v___x_2845_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
v___x_2845_ = lean_unbox(v_a_2844_);
lean_dec(v_a_2844_);
if (v___x_2845_ == 0)
{
v___y_2754_ = v_val_2842_;
v___y_2755_ = v_val_2836_;
v___y_2756_ = v___x_2843_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2846_; 
lean_dec_ref_known(v___x_2843_, 1);
v___x_2846_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2842_, v_a_2742_);
v___y_2754_ = v_val_2842_;
v___y_2755_ = v_val_2836_;
v___y_2756_ = v___x_2846_;
goto v___jp_2753_;
}
}
else
{
v___y_2754_ = v_val_2842_;
v___y_2755_ = v_val_2836_;
v___y_2756_ = v___x_2843_;
goto v___jp_2753_;
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
lean_dec(v_a_2838_);
lean_dec(v_val_2836_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2847_ = lean_box(0);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2847_);
v___x_2849_ = v___x_2840_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_val_2836_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2852_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2837_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2837_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2862_; 
lean_dec(v_a_2832_);
lean_dec(v_a_2826_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2860_ = lean_box(0);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2860_);
v___x_2862_ = v___x_2834_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2826_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2865_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2831_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2831_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2824_, v_a_2826_, v_a_2742_);
lean_dec(v_a_2826_);
lean_dec(v_a_2824_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2885_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2876_ = v___x_2873_;
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2885_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
uint8_t v___x_2878_; 
v___x_2878_ = lean_unbox(v_a_2874_);
lean_dec(v_a_2874_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_del_object(v___x_2876_);
v___x_2879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2879_, 0, v_u_2738_);
lean_ctor_set(v___x_2879_, 1, v_v_2739_);
v___x_2880_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2879_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2881_ = lean_box(0);
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v___x_2881_);
v___x_2883_ = v___x_2876_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2886_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2873_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2873_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_a_2826_);
lean_dec(v_a_2824_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2894_ = lean_ctor_get(v___y_2828_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___y_2828_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___y_2828_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___y_2828_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2824_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2906_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2825_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2825_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2914_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2823_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2823_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2924_; 
lean_dec(v_a_2813_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2922_ = lean_box(0);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2922_);
v___x_2924_ = v___x_2815_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2927_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2812_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2812_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2936_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2797_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2797_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
v___jp_2753_:
{
if (lean_obj_tag(v___y_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2787_; 
v_a_2757_ = lean_ctor_get(v___y_2756_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___y_2756_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2759_ = v___y_2756_;
v_isShared_2760_ = v_isSharedCheck_2787_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___y_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2787_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_unbox(v_a_2757_);
lean_dec(v_a_2757_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2762_ = lean_box(0);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
else
{
lean_object* v___x_2766_; 
lean_del_object(v___x_2759_);
v___x_2766_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2755_, v___y_2754_, v_a_2742_);
lean_dec_ref(v___y_2754_);
lean_dec_ref(v___y_2755_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2778_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2778_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
uint8_t v___x_2771_; 
v___x_2771_ = lean_unbox(v_a_2767_);
lean_dec(v_a_2767_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_del_object(v___x_2769_);
v___x_2772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2772_, 0, v_u_2738_);
lean_ctor_set(v___x_2772_, 1, v_v_2739_);
v___x_2773_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2772_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v___x_2774_ = lean_box(0);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2774_);
v___x_2776_ = v___x_2769_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2779_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2766_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2766_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v_v_2739_);
lean_dec(v_u_2738_);
v_a_2788_ = lean_ctor_get(v___y_2756_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___y_2756_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___y_2756_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___y_2756_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2946_, lean_object* v_v_2947_, lean_object* v_k_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2946_, v_v_2947_, v_k_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec_ref(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_k_2948_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2962_, lean_object* v_vals_2963_, lean_object* v_i_2964_, lean_object* v_k_2965_){
_start:
{
lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2970_ = lean_array_get_size(v_keys_2962_);
v___x_2971_ = lean_nat_dec_lt(v_i_2964_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
lean_dec(v_i_2964_);
v___x_2972_ = lean_box(0);
return v___x_2972_;
}
else
{
lean_object* v_fst_2973_; lean_object* v_snd_2974_; lean_object* v_k_x27_2975_; lean_object* v_fst_2976_; lean_object* v_snd_2977_; uint8_t v___x_2978_; 
v_fst_2973_ = lean_ctor_get(v_k_2965_, 0);
v_snd_2974_ = lean_ctor_get(v_k_2965_, 1);
v_k_x27_2975_ = lean_array_fget_borrowed(v_keys_2962_, v_i_2964_);
v_fst_2976_ = lean_ctor_get(v_k_x27_2975_, 0);
v_snd_2977_ = lean_ctor_get(v_k_x27_2975_, 1);
v___x_2978_ = lean_nat_dec_eq(v_fst_2973_, v_fst_2976_);
if (v___x_2978_ == 0)
{
goto v___jp_2966_;
}
else
{
uint8_t v___x_2979_; 
v___x_2979_ = lean_nat_dec_eq(v_snd_2974_, v_snd_2977_);
if (v___x_2979_ == 0)
{
goto v___jp_2966_;
}
else
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = lean_array_fget_borrowed(v_vals_2963_, v_i_2964_);
lean_dec(v_i_2964_);
lean_inc(v___x_2980_);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
return v___x_2981_;
}
}
}
v___jp_2966_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_nat_add(v_i_2964_, v___x_2967_);
lean_dec(v_i_2964_);
v_i_2964_ = v___x_2968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2982_, lean_object* v_vals_2983_, lean_object* v_i_2984_, lean_object* v_k_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2982_, v_vals_2983_, v_i_2984_, v_k_2985_);
lean_dec_ref(v_k_2985_);
lean_dec_ref(v_vals_2983_);
lean_dec_ref(v_keys_2982_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2987_, size_t v_x_2988_, lean_object* v_x_2989_){
_start:
{
if (lean_obj_tag(v_x_2987_) == 0)
{
lean_object* v_es_2990_; lean_object* v___x_2991_; size_t v___x_2992_; size_t v___x_2993_; lean_object* v_j_2994_; lean_object* v___x_2995_; 
v_es_2990_ = lean_ctor_get(v_x_2987_, 0);
v___x_2991_ = lean_box(2);
v___x_2992_ = ((size_t)31ULL);
v___x_2993_ = lean_usize_land(v_x_2988_, v___x_2992_);
v_j_2994_ = lean_usize_to_nat(v___x_2993_);
v___x_2995_ = lean_array_get_borrowed(v___x_2991_, v_es_2990_, v_j_2994_);
lean_dec(v_j_2994_);
switch(lean_obj_tag(v___x_2995_))
{
case 0:
{
lean_object* v_key_2996_; lean_object* v_val_2997_; lean_object* v_fst_2998_; lean_object* v_snd_2999_; lean_object* v_fst_3000_; lean_object* v_snd_3001_; uint8_t v___x_3002_; 
v_key_2996_ = lean_ctor_get(v___x_2995_, 0);
v_val_2997_ = lean_ctor_get(v___x_2995_, 1);
v_fst_2998_ = lean_ctor_get(v_x_2989_, 0);
v_snd_2999_ = lean_ctor_get(v_x_2989_, 1);
v_fst_3000_ = lean_ctor_get(v_key_2996_, 0);
v_snd_3001_ = lean_ctor_get(v_key_2996_, 1);
v___x_3002_ = lean_nat_dec_eq(v_fst_2998_, v_fst_3000_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = lean_box(0);
return v___x_3003_;
}
else
{
uint8_t v___x_3004_; 
v___x_3004_ = lean_nat_dec_eq(v_snd_2999_, v_snd_3001_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; 
v___x_3005_ = lean_box(0);
return v___x_3005_;
}
else
{
lean_object* v___x_3006_; 
lean_inc(v_val_2997_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v_val_2997_);
return v___x_3006_;
}
}
}
case 1:
{
lean_object* v_node_3007_; size_t v___x_3008_; size_t v___x_3009_; 
v_node_3007_ = lean_ctor_get(v___x_2995_, 0);
v___x_3008_ = ((size_t)5ULL);
v___x_3009_ = lean_usize_shift_right(v_x_2988_, v___x_3008_);
v_x_2987_ = v_node_3007_;
v_x_2988_ = v___x_3009_;
goto _start;
}
default: 
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_box(0);
return v___x_3011_;
}
}
}
else
{
lean_object* v_ks_3012_; lean_object* v_vs_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_ks_3012_ = lean_ctor_get(v_x_2987_, 0);
v_vs_3013_ = lean_ctor_get(v_x_2987_, 1);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_3012_, v_vs_3013_, v___x_3014_, v_x_2989_);
return v___x_3015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_3016_, lean_object* v_x_3017_, lean_object* v_x_3018_){
_start:
{
size_t v_x_3987__boxed_3019_; lean_object* v_res_3020_; 
v_x_3987__boxed_3019_ = lean_unbox_usize(v_x_3017_);
lean_dec(v_x_3017_);
v_res_3020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3016_, v_x_3987__boxed_3019_, v_x_3018_);
lean_dec_ref(v_x_3018_);
lean_dec_ref(v_x_3016_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
lean_object* v_fst_3023_; lean_object* v_snd_3024_; uint64_t v___x_3025_; uint64_t v___x_3026_; uint64_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v_fst_3023_ = lean_ctor_get(v_x_3022_, 0);
v_snd_3024_ = lean_ctor_get(v_x_3022_, 1);
v___x_3025_ = lean_uint64_of_nat(v_fst_3023_);
v___x_3026_ = lean_uint64_of_nat(v_snd_3024_);
v___x_3027_ = lean_uint64_mix_hash(v___x_3025_, v___x_3026_);
v___x_3028_ = lean_uint64_to_usize(v___x_3027_);
v___x_3029_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3021_, v___x_3028_, v_x_3022_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3030_, lean_object* v_x_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3030_, v_x_3031_);
lean_dec_ref(v_x_3031_);
lean_dec_ref(v_x_3030_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3033_, lean_object* v_v_3034_, lean_object* v_k_3035_, lean_object* v_as_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
if (lean_obj_tag(v_as_3036_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec_ref(v_k_3035_);
lean_dec(v_v_3034_);
lean_dec(v_u_3033_);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v_head_3051_; lean_object* v_tail_3052_; lean_object* v_fst_3053_; lean_object* v_snd_3054_; lean_object* v___x_3055_; 
v_head_3051_ = lean_ctor_get(v_as_3036_, 0);
lean_inc(v_head_3051_);
v_tail_3052_ = lean_ctor_get(v_as_3036_, 1);
lean_inc(v_tail_3052_);
lean_dec_ref_known(v_as_3036_, 2);
v_fst_3053_ = lean_ctor_get(v_head_3051_, 0);
lean_inc(v_fst_3053_);
v_snd_3054_ = lean_ctor_get(v_head_3051_, 1);
lean_inc(v_snd_3054_);
lean_dec(v_head_3051_);
lean_inc_ref(v_k_3035_);
lean_inc(v_v_3034_);
lean_inc(v_u_3033_);
v___x_3055_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3033_, v_v_3034_, v_k_3035_, v_fst_3053_, v_snd_3054_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_dec_ref_known(v___x_3055_, 1);
v_as_3036_ = v_tail_3052_;
goto _start;
}
else
{
lean_dec(v_tail_3052_);
lean_dec_ref(v_k_3035_);
lean_dec(v_v_3034_);
lean_dec(v_u_3033_);
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3057_, lean_object* v_v_3058_, lean_object* v_k_3059_, lean_object* v_as_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v_res_3073_; 
v_res_3073_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3057_, v_v_3058_, v_k_3059_, v_as_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec(v___y_3061_);
return v_res_3073_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3074_, lean_object* v_v_3075_, lean_object* v_k_3076_, lean_object* v_as_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
if (lean_obj_tag(v_as_3077_) == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v_k_3076_);
lean_dec(v_v_3075_);
lean_dec(v_u_3074_);
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
else
{
lean_object* v_head_3092_; lean_object* v_tail_3093_; lean_object* v_fst_3094_; lean_object* v_snd_3095_; lean_object* v___x_3096_; 
v_head_3092_ = lean_ctor_get(v_as_3077_, 0);
lean_inc(v_head_3092_);
v_tail_3093_ = lean_ctor_get(v_as_3077_, 1);
lean_inc(v_tail_3093_);
lean_dec_ref_known(v_as_3077_, 2);
v_fst_3094_ = lean_ctor_get(v_head_3092_, 0);
lean_inc(v_fst_3094_);
v_snd_3095_ = lean_ctor_get(v_head_3092_, 1);
lean_inc(v_snd_3095_);
lean_dec(v_head_3092_);
lean_inc_ref(v_k_3076_);
lean_inc(v_v_3075_);
lean_inc(v_u_3074_);
v___x_3096_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3074_, v_v_3075_, v_k_3076_, v_fst_3094_, v_snd_3095_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_dec_ref_known(v___x_3096_, 1);
v_as_3077_ = v_tail_3093_;
goto _start;
}
else
{
lean_dec(v_tail_3093_);
lean_dec_ref(v_k_3076_);
lean_dec(v_v_3075_);
lean_dec(v_u_3074_);
return v___x_3096_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3098_, lean_object* v_v_3099_, lean_object* v_k_3100_, lean_object* v_as_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3098_, v_v_3099_, v_k_3100_, v_as_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3111_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec(v___y_3102_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3115_, lean_object* v_v_3116_, lean_object* v_k_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v_cnstrsOf_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v_cnstrsOf_3150_ = lean_ctor_get(v_a_3149_, 17);
lean_inc_ref(v_cnstrsOf_3150_);
lean_dec(v_a_3149_);
lean_inc(v_v_3116_);
lean_inc(v_u_3115_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v_u_3115_);
lean_ctor_set(v___x_3151_, 1, v_v_3116_);
v___x_3152_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3150_, v___x_3151_);
lean_dec_ref_known(v___x_3151_, 2);
lean_dec_ref(v_cnstrsOf_3150_);
if (lean_obj_tag(v___x_3152_) == 1)
{
lean_object* v_val_3153_; lean_object* v___x_3154_; 
v_val_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_val_3153_);
lean_dec_ref_known(v___x_3152_, 1);
lean_inc_ref(v_k_3117_);
lean_inc(v_v_3116_);
lean_inc(v_u_3115_);
v___x_3154_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3115_, v_v_3116_, v_k_3117_, v_val_3153_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
goto v___jp_3130_;
}
else
{
lean_dec_ref(v_k_3117_);
lean_dec(v_v_3116_);
lean_dec(v_u_3115_);
return v___x_3154_;
}
}
else
{
lean_dec(v___x_3152_);
goto v___jp_3130_;
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_k_3117_);
lean_dec(v_v_3116_);
lean_dec(v_u_3115_);
v_a_3155_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3148_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3148_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
v___jp_3130_:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v_cnstrsOf_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_a_3132_);
lean_dec_ref_known(v___x_3131_, 1);
v_cnstrsOf_3133_ = lean_ctor_get(v_a_3132_, 17);
lean_inc_ref(v_cnstrsOf_3133_);
lean_dec(v_a_3132_);
lean_inc(v_u_3115_);
lean_inc(v_v_3116_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v_v_3116_);
lean_ctor_set(v___x_3134_, 1, v_u_3115_);
v___x_3135_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3133_, v___x_3134_);
lean_dec_ref_known(v___x_3134_, 2);
lean_dec_ref(v_cnstrsOf_3133_);
if (lean_obj_tag(v___x_3135_) == 1)
{
lean_object* v_val_3136_; lean_object* v___x_3137_; 
v_val_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_val_3136_);
lean_dec_ref_known(v___x_3135_, 1);
lean_inc_ref(v_k_3117_);
lean_inc(v_v_3116_);
lean_inc(v_u_3115_);
v___x_3137_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3115_, v_v_3116_, v_k_3117_, v_val_3136_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3138_; 
lean_dec_ref_known(v___x_3137_, 1);
v___x_3138_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3115_, v_v_3116_, v_k_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec_ref(v_k_3117_);
return v___x_3138_;
}
else
{
lean_dec_ref(v_k_3117_);
lean_dec(v_v_3116_);
lean_dec(v_u_3115_);
return v___x_3137_;
}
}
else
{
lean_object* v___x_3139_; 
lean_dec(v___x_3135_);
v___x_3139_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3115_, v_v_3116_, v_k_3117_, v_a_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec_ref(v_k_3117_);
return v___x_3139_;
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_k_3117_);
lean_dec(v_v_3116_);
lean_dec(v_u_3115_);
v_a_3140_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3131_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3131_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3163_, lean_object* v_v_3164_, lean_object* v_k_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v_res_3178_; 
v_res_3178_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3163_, v_v_3164_, v_k_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, v_a_3176_);
lean_dec(v_a_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec(v_a_3167_);
lean_dec(v_a_3166_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3180_, v_x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3183_, v_x_3184_, v_x_3185_);
lean_dec_ref(v_x_3185_);
lean_dec_ref(v_x_3184_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3187_, lean_object* v_x_3188_, size_t v_x_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3188_, v_x_3189_, v_x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3192_, lean_object* v_x_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
size_t v_x_4251__boxed_3196_; lean_object* v_res_3197_; 
v_x_4251__boxed_3196_ = lean_unbox_usize(v_x_3194_);
lean_dec(v_x_3194_);
v_res_3197_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3192_, v_x_3193_, v_x_4251__boxed_3196_, v_x_3195_);
lean_dec_ref(v_x_3195_);
lean_dec_ref(v_x_3193_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3198_, lean_object* v_keys_3199_, lean_object* v_vals_3200_, lean_object* v_heq_3201_, lean_object* v_i_3202_, lean_object* v_k_3203_){
_start:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3199_, v_vals_3200_, v_i_3202_, v_k_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3205_, lean_object* v_keys_3206_, lean_object* v_vals_3207_, lean_object* v_heq_3208_, lean_object* v_i_3209_, lean_object* v_k_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3205_, v_keys_3206_, v_vals_3207_, v_heq_3208_, v_i_3209_, v_k_3210_);
lean_dec_ref(v_k_3210_);
lean_dec_ref(v_vals_3207_);
lean_dec_ref(v_keys_3206_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3212_, lean_object* v_v_3213_, lean_object* v_k_3214_, lean_object* v_w_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v___x_3228_; 
v___x_3228_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3212_, v_v_3213_, v_k_3214_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3251_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3231_ = v___x_3228_;
v_isShared_3232_ = v_isSharedCheck_3251_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_a_3229_);
lean_dec(v___x_3228_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3251_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
uint8_t v___x_3233_; 
v___x_3233_ = lean_unbox(v_a_3229_);
lean_dec(v_a_3229_);
if (v___x_3233_ == 0)
{
lean_object* v___x_3234_; lean_object* v___x_3236_; 
lean_dec_ref(v_k_3214_);
lean_dec(v_v_3213_);
lean_dec(v_u_3212_);
v___x_3234_ = lean_box(0);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3234_);
v___x_3236_ = v___x_3231_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3234_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
else
{
lean_object* v___x_3238_; 
lean_del_object(v___x_3231_);
lean_inc_ref(v_k_3214_);
lean_inc(v_v_3213_);
lean_inc(v_u_3212_);
v___x_3238_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3212_, v_v_3213_, v_k_3214_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v___x_3239_; 
lean_dec_ref_known(v___x_3238_, 1);
v___x_3239_ = l_Lean_Meta_Grind_Order_getProof(v_w_3215_, v_v_3213_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref_known(v___x_3239_, 1);
lean_inc(v_v_3213_);
lean_inc(v_u_3212_);
v___x_3241_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3212_, v_v_3213_, v_a_3240_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v___x_3242_; 
lean_dec_ref_known(v___x_3241_, 1);
v___x_3242_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3212_, v_v_3213_, v_k_3214_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v___x_3242_;
}
else
{
lean_dec_ref(v_k_3214_);
lean_dec(v_v_3213_);
lean_dec(v_u_3212_);
return v___x_3241_;
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_k_3214_);
lean_dec(v_v_3213_);
lean_dec(v_u_3212_);
v_a_3243_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3239_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3239_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_dec_ref(v_k_3214_);
lean_dec(v_v_3213_);
lean_dec(v_u_3212_);
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v_k_3214_);
lean_dec(v_v_3213_);
lean_dec(v_u_3212_);
v_a_3252_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3228_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3228_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3260_, lean_object* v_v_3261_, lean_object* v_k_3262_, lean_object* v_w_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3260_, v_v_3261_, v_k_3262_, v_w_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec(v_w_3263_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3277_, lean_object* v_i_3278_, lean_object* v_v_3279_, lean_object* v_x_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
if (lean_obj_tag(v_x_3280_) == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_i_3278_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
else
{
lean_object* v_key_3295_; lean_object* v_value_3296_; lean_object* v_tail_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_key_3295_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_key_3295_);
v_value_3296_ = lean_ctor_get(v_x_3280_, 1);
lean_inc(v_value_3296_);
v_tail_3297_ = lean_ctor_get(v_x_3280_, 2);
lean_inc(v_tail_3297_);
lean_dec_ref_known(v_x_3280_, 3);
v___x_3298_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3277_, v_value_3296_);
lean_inc(v_i_3278_);
v___x_3299_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3278_, v_key_3295_, v___x_3298_, v_v_3279_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_dec_ref_known(v___x_3299_, 1);
v_x_3280_ = v_tail_3297_;
goto _start;
}
else
{
lean_dec(v_tail_3297_);
lean_dec(v_i_3278_);
return v___x_3299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3301_, lean_object* v_i_3302_, lean_object* v_v_3303_, lean_object* v_x_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3301_, v_i_3302_, v_v_3303_, v_x_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
lean_dec_ref(v___y_3310_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec(v_v_3303_);
lean_dec_ref(v___x_3301_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3318_, lean_object* v_v_3319_, lean_object* v_u_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
if (lean_obj_tag(v_x_3321_) == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v_v_3319_);
lean_dec_ref(v_k_3318_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
return v___x_3335_;
}
else
{
lean_object* v_key_3336_; lean_object* v_value_3337_; lean_object* v_tail_3338_; lean_object* v___y_3340_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_key_3336_ = lean_ctor_get(v_x_3321_, 0);
lean_inc_n(v_key_3336_, 2);
v_value_3337_ = lean_ctor_get(v_x_3321_, 1);
lean_inc(v_value_3337_);
v_tail_3338_ = lean_ctor_get(v_x_3321_, 2);
lean_inc(v_tail_3338_);
lean_dec_ref_known(v_x_3321_, 3);
lean_inc_ref(v_k_3318_);
v___x_3342_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3337_, v_k_3318_);
lean_dec(v_value_3337_);
lean_inc_ref(v___x_3342_);
lean_inc(v_v_3319_);
v___x_3343_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3336_, v_v_3319_, v___x_3342_, v_u_3320_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref_known(v___x_3343_, 1);
v___x_3344_ = l_Lean_Meta_Grind_Order_getStruct(v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v_targets_3346_; lean_object* v_size_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v_targets_3346_ = lean_ctor_get(v_a_3345_, 19);
lean_inc_ref(v_targets_3346_);
lean_dec(v_a_3345_);
v_size_3347_ = lean_ctor_get(v_targets_3346_, 2);
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_nat_dec_lt(v_v_3319_, v_size_3347_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v_targets_3346_);
v___x_3350_ = l_outOfBounds___redArg(v___x_3348_);
v___x_3351_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3342_, v_key_3336_, v_v_3319_, v___x_3350_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec_ref(v___x_3342_);
v___y_3340_ = v___x_3351_;
goto v___jp_3339_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3348_, v_targets_3346_, v_v_3319_);
lean_dec_ref(v_targets_3346_);
v___x_3353_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3342_, v_key_3336_, v_v_3319_, v___x_3352_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec_ref(v___x_3342_);
v___y_3340_ = v___x_3353_;
goto v___jp_3339_;
}
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v___x_3342_);
lean_dec(v_tail_3338_);
lean_dec(v_key_3336_);
lean_dec(v_v_3319_);
lean_dec_ref(v_k_3318_);
v_a_3354_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3344_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3344_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
}
else
{
lean_dec_ref(v___x_3342_);
lean_dec(v_key_3336_);
v___y_3340_ = v___x_3343_;
goto v___jp_3339_;
}
v___jp_3339_:
{
if (lean_obj_tag(v___y_3340_) == 0)
{
lean_dec_ref_known(v___y_3340_, 1);
v_x_3321_ = v_tail_3338_;
goto _start;
}
else
{
lean_dec(v_tail_3338_);
lean_dec(v_v_3319_);
lean_dec_ref(v_k_3318_);
return v___y_3340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3362_, lean_object* v_v_3363_, lean_object* v_u_3364_, lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3362_, v_v_3363_, v_u_3364_, v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec(v_u_3364_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3379_, lean_object* v_v_3380_, lean_object* v_k_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v___y_3395_; lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v_targets_3416_; lean_object* v_size_3417_; lean_object* v___x_3418_; uint8_t v___x_3419_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v_targets_3416_ = lean_ctor_get(v_a_3415_, 19);
lean_inc_ref(v_targets_3416_);
lean_dec(v_a_3415_);
v_size_3417_ = lean_ctor_get(v_targets_3416_, 2);
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_nat_dec_lt(v_v_3380_, v_size_3417_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref(v_targets_3416_);
v___x_3420_ = l_outOfBounds___redArg(v___x_3418_);
lean_inc(v_u_3379_);
v___x_3421_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3381_, v_u_3379_, v_v_3380_, v___x_3420_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
v___y_3395_ = v___x_3421_;
goto v___jp_3394_;
}
else
{
lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3422_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3418_, v_targets_3416_, v_v_3380_);
lean_dec_ref(v_targets_3416_);
lean_inc(v_u_3379_);
v___x_3423_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3381_, v_u_3379_, v_v_3380_, v___x_3422_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
v___y_3395_ = v___x_3423_;
goto v___jp_3394_;
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_k_3381_);
lean_dec(v_v_3380_);
lean_dec(v_u_3379_);
v_a_3424_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3414_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3414_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
v___jp_3394_:
{
if (lean_obj_tag(v___y_3395_) == 0)
{
lean_object* v___x_3396_; 
lean_dec_ref_known(v___y_3395_, 1);
v___x_3396_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v_sources_3398_; lean_object* v_size_3399_; lean_object* v___x_3400_; uint8_t v___x_3401_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v_sources_3398_ = lean_ctor_get(v_a_3397_, 18);
lean_inc_ref(v_sources_3398_);
lean_dec(v_a_3397_);
v_size_3399_ = lean_ctor_get(v_sources_3398_, 2);
v___x_3400_ = lean_box(0);
v___x_3401_ = lean_nat_dec_lt(v_u_3379_, v_size_3399_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref(v_sources_3398_);
v___x_3402_ = l_outOfBounds___redArg(v___x_3400_);
v___x_3403_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3381_, v_v_3380_, v_u_3379_, v___x_3402_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_u_3379_);
return v___x_3403_;
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3400_, v_sources_3398_, v_u_3379_);
lean_dec_ref(v_sources_3398_);
v___x_3405_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3381_, v_v_3380_, v_u_3379_, v___x_3404_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
lean_dec(v_u_3379_);
return v___x_3405_;
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v_k_3381_);
lean_dec(v_v_3380_);
lean_dec(v_u_3379_);
v_a_3406_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3396_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3396_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_dec_ref(v_k_3381_);
lean_dec(v_v_3380_);
lean_dec(v_u_3379_);
return v___y_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3432_, lean_object* v_v_3433_, lean_object* v_k_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3432_, v_v_3433_, v_k_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3444_);
lean_dec(v_a_3443_);
lean_dec_ref(v_a_3442_);
lean_dec(v_a_3441_);
lean_dec_ref(v_a_3440_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec(v_a_3435_);
return v_res_3447_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3454_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3456_ = l_Lean_Name_append(v___x_3455_, v___x_3454_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3457_, lean_object* v_v_3458_, lean_object* v_k_3459_, lean_object* v_h_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3462_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3626_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3551_ = v___x_3548_;
v_isShared_3552_ = v_isSharedCheck_3626_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3548_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3626_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
uint8_t v___x_3553_; 
v___x_3553_ = lean_unbox(v_a_3549_);
lean_dec(v_a_3549_);
if (v___x_3553_ == 0)
{
uint8_t v___x_3554_; 
lean_del_object(v___x_3551_);
v___x_3554_ = lean_nat_dec_eq(v_u_3457_, v_v_3458_);
if (v___x_3554_ == 0)
{
lean_object* v_toCold_3555_; lean_object* v_options_3556_; uint8_t v_hasTrace_3557_; 
v_toCold_3555_ = lean_ctor_get(v_a_3470_, 0);
v_options_3556_ = lean_ctor_get(v_toCold_3555_, 2);
v_hasTrace_3557_ = lean_ctor_get_uint8(v_options_3556_, sizeof(void*)*1);
if (v_hasTrace_3557_ == 0)
{
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
v___y_3518_ = v_a_3468_;
v___y_3519_ = v_a_3469_;
v___y_3520_ = v_a_3470_;
v___y_3521_ = v_a_3471_;
goto v___jp_3510_;
}
else
{
lean_object* v_inheritedTraceOptions_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; uint8_t v___x_3561_; 
v_inheritedTraceOptions_3558_ = lean_ctor_get(v_toCold_3555_, 11);
v___x_3559_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3560_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3558_, v_options_3556_, v___x_3560_);
if (v___x_3561_ == 0)
{
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
v___y_3518_ = v_a_3468_;
v___y_3519_ = v_a_3469_;
v___y_3520_ = v_a_3470_;
v___y_3521_ = v_a_3471_;
goto v___jp_3510_;
}
else
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3457_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
lean_dec_ref_known(v___x_3562_, 1);
v___x_3564_ = l_Lean_Meta_Grind_Order_getExpr(v_v_3458_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v_k_3566_; uint8_t v_strict_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___y_3575_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v_k_3566_ = lean_ctor_get(v_k_3459_, 0);
v_strict_3567_ = lean_ctor_get_uint8(v_k_3459_, sizeof(void*)*1);
v___x_3568_ = l_Lean_MessageData_ofExpr(v_a_3563_);
v___x_3569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3568_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l_Lean_MessageData_ofExpr(v_a_3565_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___x_3569_);
if (v_strict_3567_ == 0)
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Int_repr(v_k_3566_);
v___y_3575_ = v___x_3580_;
goto v___jp_3574_;
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3581_ = l_Int_repr(v_k_3566_);
v___x_3582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3583_ = lean_string_append(v___x_3581_, v___x_3582_);
v___y_3575_ = v___x_3583_;
goto v___jp_3574_;
}
v___jp_3574_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3576_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3576_, 0, v___y_3575_);
v___x_3577_ = l_Lean_MessageData_ofFormat(v___x_3576_);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3573_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3559_, v___x_3578_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_dec_ref_known(v___x_3579_, 1);
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
v___y_3513_ = v_a_3463_;
v___y_3514_ = v_a_3464_;
v___y_3515_ = v_a_3465_;
v___y_3516_ = v_a_3466_;
v___y_3517_ = v_a_3467_;
v___y_3518_ = v_a_3468_;
v___y_3519_ = v_a_3469_;
v___y_3520_ = v_a_3470_;
v___y_3521_ = v_a_3471_;
goto v___jp_3510_;
}
else
{
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
return v___x_3579_;
}
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_a_3563_);
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v_a_3584_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3564_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3564_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v_a_3592_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3562_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3562_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
}
}
else
{
uint8_t v___x_3600_; 
lean_dec(v_v_3458_);
v___x_3600_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3459_);
if (v___x_3600_ == 0)
{
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_u_3457_);
goto v___jp_3545_;
}
else
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3457_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
lean_dec(v_u_3457_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
v___x_3603_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3602_, v_k_3459_, v_h_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
lean_dec_ref(v_k_3459_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_a_3604_; lean_object* v___x_3605_; 
v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_a_3604_);
lean_dec_ref_known(v___x_3603_, 1);
v___x_3605_ = l_Lean_Meta_Grind_closeGoal(v_a_3604_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_dec_ref_known(v___x_3605_, 1);
goto v___jp_3545_;
}
else
{
return v___x_3605_;
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_a_3606_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3603_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3603_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
v_a_3614_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3601_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3601_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
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
}
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v___x_3622_ = lean_box(0);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3622_);
v___x_3624_ = v___x_3551_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v_a_3627_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3548_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3548_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
v___jp_3473_:
{
lean_object* v___x_3485_; 
v___x_3485_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3457_, v_v_3458_, v_k_3459_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3501_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3501_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3501_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
uint8_t v___x_3490_; 
v___x_3490_ = lean_unbox(v_a_3486_);
lean_dec(v_a_3486_);
if (v___x_3490_ == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3493_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v___x_3491_ = lean_box(0);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3491_);
v___x_3493_ = v___x_3488_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3491_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
else
{
lean_object* v___x_3495_; 
lean_del_object(v___x_3488_);
lean_inc_ref(v_k_3459_);
lean_inc(v_v_3458_);
lean_inc(v_u_3457_);
v___x_3495_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3457_, v_v_3458_, v_k_3459_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
lean_dec_ref_known(v___x_3495_, 1);
lean_inc_ref(v_k_3459_);
lean_inc_n(v_u_3457_, 2);
v___x_3496_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3496_, 0, v_u_3457_);
lean_ctor_set(v___x_3496_, 1, v_k_3459_);
lean_ctor_set(v___x_3496_, 2, v_h_3460_);
lean_inc(v_v_3458_);
v___x_3497_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3457_, v_v_3458_, v___x_3496_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v___x_3498_; 
lean_dec_ref_known(v___x_3497_, 1);
lean_inc_ref(v_k_3459_);
lean_inc(v_v_3458_);
lean_inc(v_u_3457_);
v___x_3498_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3457_, v_v_3458_, v_k_3459_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v___x_3499_; 
lean_dec_ref_known(v___x_3498_, 1);
v___x_3499_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3457_, v_v_3458_, v_k_3459_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v___x_3500_; 
lean_dec_ref_known(v___x_3499_, 1);
v___x_3500_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
return v___x_3500_;
}
else
{
return v___x_3499_;
}
}
else
{
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
return v___x_3498_;
}
}
else
{
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
return v___x_3497_;
}
}
else
{
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v_a_3502_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3485_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3485_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3507_; 
if (v_isShared_3505_ == 0)
{
v___x_3507_ = v___x_3504_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
v___jp_3510_:
{
lean_object* v___x_3522_; 
v___x_3522_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_3458_, v_u_3457_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
if (lean_obj_tag(v_a_3523_) == 1)
{
lean_object* v_val_3524_; lean_object* v___x_3525_; uint8_t v___x_3526_; 
v_val_3524_ = lean_ctor_get(v_a_3523_, 0);
lean_inc_n(v_val_3524_, 2);
lean_dec_ref_known(v_a_3523_, 1);
v___x_3525_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3459_, v_val_3524_);
v___x_3526_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3525_);
lean_dec_ref(v___x_3525_);
if (v___x_3526_ == 0)
{
lean_dec(v_val_3524_);
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
v___y_3476_ = v___y_3513_;
v___y_3477_ = v___y_3514_;
v___y_3478_ = v___y_3515_;
v___y_3479_ = v___y_3516_;
v___y_3480_ = v___y_3517_;
v___y_3481_ = v___y_3518_;
v___y_3482_ = v___y_3519_;
v___y_3483_ = v___y_3520_;
v___y_3484_ = v___y_3521_;
goto v___jp_3473_;
}
else
{
lean_object* v___x_3527_; 
v___x_3527_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3457_, v_v_3458_, v_k_3459_, v_h_3460_, v_val_3524_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v_val_3524_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3535_; 
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3535_ == 0)
{
lean_object* v_unused_3536_; 
v_unused_3536_ = lean_ctor_get(v___x_3527_, 0);
lean_dec(v_unused_3536_);
v___x_3529_ = v___x_3527_;
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
else
{
lean_dec(v___x_3527_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3535_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3531_; lean_object* v___x_3533_; 
v___x_3531_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3531_);
v___x_3533_ = v___x_3529_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
else
{
return v___x_3527_;
}
}
}
else
{
lean_dec(v_a_3523_);
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
v___y_3476_ = v___y_3513_;
v___y_3477_ = v___y_3514_;
v___y_3478_ = v___y_3515_;
v___y_3479_ = v___y_3516_;
v___y_3480_ = v___y_3517_;
v___y_3481_ = v___y_3518_;
v___y_3482_ = v___y_3519_;
v___y_3483_ = v___y_3520_;
v___y_3484_ = v___y_3521_;
goto v___jp_3473_;
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v_h_3460_);
lean_dec_ref(v_k_3459_);
lean_dec(v_v_3458_);
lean_dec(v_u_3457_);
v_a_3537_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3522_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3522_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
v___jp_3545_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = lean_box(0);
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
return v___x_3547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3635_, lean_object* v_v_3636_, lean_object* v_k_3637_, lean_object* v_h_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3635_, v_v_3636_, v_k_3637_, v_h_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec(v_a_3639_);
return v_res_3651_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_box(0);
v___x_3659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3660_ = l_Lean_mkConst(v___x_3659_, v___x_3658_);
return v___x_3660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_cls_3666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3668_ = l_Lean_Name_append(v___x_3667_, v_cls_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3669_, lean_object* v_e_3670_, lean_object* v_he_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; uint8_t v___y_3700_; lean_object* v_h_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v_toCold_3744_; lean_object* v_options_3745_; uint8_t v_hasTrace_3746_; 
v_toCold_3744_ = lean_ctor_get(v_a_3681_, 0);
v_options_3745_ = lean_ctor_get(v_toCold_3744_, 2);
v_hasTrace_3746_ = lean_ctor_get_uint8(v_options_3745_, sizeof(void*)*1);
if (v_hasTrace_3746_ == 0)
{
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
v___y_3732_ = v_a_3678_;
v___y_3733_ = v_a_3679_;
v___y_3734_ = v_a_3680_;
v___y_3735_ = v_a_3681_;
v___y_3736_ = v_a_3682_;
goto v___jp_3725_;
}
else
{
lean_object* v_inheritedTraceOptions_3747_; lean_object* v_cls_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v_inheritedTraceOptions_3747_ = lean_ctor_get(v_toCold_3744_, 11);
v_cls_3748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3747_, v_options_3745_, v___x_3749_);
if (v___x_3750_ == 0)
{
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
v___y_3732_ = v_a_3678_;
v___y_3733_ = v_a_3679_;
v___y_3734_ = v_a_3680_;
v___y_3735_ = v_a_3681_;
v___y_3736_ = v_a_3682_;
goto v___jp_3725_;
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3669_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3753_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3748_, v_a_3752_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_);
if (lean_obj_tag(v___x_3753_) == 0)
{
lean_dec_ref_known(v___x_3753_, 1);
v___y_3726_ = v_a_3672_;
v___y_3727_ = v_a_3673_;
v___y_3728_ = v_a_3674_;
v___y_3729_ = v_a_3675_;
v___y_3730_ = v_a_3676_;
v___y_3731_ = v_a_3677_;
v___y_3732_ = v_a_3678_;
v___y_3733_ = v_a_3679_;
v___y_3734_ = v_a_3680_;
v___y_3735_ = v_a_3681_;
v___y_3736_ = v_a_3682_;
goto v___jp_3725_;
}
else
{
lean_dec_ref(v_he_3671_);
lean_dec_ref(v_e_3670_);
lean_dec_ref(v_c_3669_);
return v___x_3753_;
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec_ref(v_he_3671_);
lean_dec_ref(v_e_3670_);
lean_dec_ref(v_c_3669_);
v_a_3754_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3751_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3751_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
v___jp_3684_:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3701_, 0, v___y_3699_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*1, v___y_3700_);
v___x_3702_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3693_, v___y_3689_, v___x_3701_, v___y_3688_, v___y_3695_, v___y_3690_, v___y_3698_, v___y_3686_, v___y_3696_, v___y_3691_, v___y_3685_, v___y_3694_, v___y_3692_, v___y_3687_, v___y_3697_);
return v___x_3702_;
}
v___jp_3703_:
{
uint8_t v_kind_3716_; 
v_kind_3716_ = lean_ctor_get_uint8(v_c_3669_, sizeof(void*)*5);
if (v_kind_3716_ == 1)
{
lean_object* v_u_3717_; lean_object* v_v_3718_; lean_object* v_k_3719_; uint8_t v___x_3720_; 
v_u_3717_ = lean_ctor_get(v_c_3669_, 0);
lean_inc(v_u_3717_);
v_v_3718_ = lean_ctor_get(v_c_3669_, 1);
lean_inc(v_v_3718_);
v_k_3719_ = lean_ctor_get(v_c_3669_, 2);
lean_inc(v_k_3719_);
lean_dec_ref(v_c_3669_);
v___x_3720_ = 1;
v___y_3685_ = v___y_3711_;
v___y_3686_ = v___y_3708_;
v___y_3687_ = v___y_3714_;
v___y_3688_ = v_h_3704_;
v___y_3689_ = v_v_3718_;
v___y_3690_ = v___y_3706_;
v___y_3691_ = v___y_3710_;
v___y_3692_ = v___y_3713_;
v___y_3693_ = v_u_3717_;
v___y_3694_ = v___y_3712_;
v___y_3695_ = v___y_3705_;
v___y_3696_ = v___y_3709_;
v___y_3697_ = v___y_3715_;
v___y_3698_ = v___y_3707_;
v___y_3699_ = v_k_3719_;
v___y_3700_ = v___x_3720_;
goto v___jp_3684_;
}
else
{
lean_object* v_u_3721_; lean_object* v_v_3722_; lean_object* v_k_3723_; uint8_t v___x_3724_; 
v_u_3721_ = lean_ctor_get(v_c_3669_, 0);
lean_inc(v_u_3721_);
v_v_3722_ = lean_ctor_get(v_c_3669_, 1);
lean_inc(v_v_3722_);
v_k_3723_ = lean_ctor_get(v_c_3669_, 2);
lean_inc(v_k_3723_);
lean_dec_ref(v_c_3669_);
v___x_3724_ = 0;
v___y_3685_ = v___y_3711_;
v___y_3686_ = v___y_3708_;
v___y_3687_ = v___y_3714_;
v___y_3688_ = v_h_3704_;
v___y_3689_ = v_v_3722_;
v___y_3690_ = v___y_3706_;
v___y_3691_ = v___y_3710_;
v___y_3692_ = v___y_3713_;
v___y_3693_ = v_u_3721_;
v___y_3694_ = v___y_3712_;
v___y_3695_ = v___y_3705_;
v___y_3696_ = v___y_3709_;
v___y_3697_ = v___y_3715_;
v___y_3698_ = v___y_3707_;
v___y_3699_ = v_k_3723_;
v___y_3700_ = v___x_3724_;
goto v___jp_3684_;
}
}
v___jp_3725_:
{
lean_object* v_h_x3f_3737_; 
v_h_x3f_3737_ = lean_ctor_get(v_c_3669_, 4);
if (lean_obj_tag(v_h_x3f_3737_) == 1)
{
lean_object* v_e_3738_; lean_object* v_val_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_e_3738_ = lean_ctor_get(v_c_3669_, 3);
v_val_3739_ = lean_ctor_get(v_h_x3f_3737_, 0);
v___x_3740_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3670_);
v___x_3741_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3670_, v_he_3671_);
lean_inc(v_val_3739_);
lean_inc_ref(v_e_3738_);
v___x_3742_ = l_Lean_mkApp4(v___x_3740_, v_e_3670_, v_e_3738_, v_val_3739_, v___x_3741_);
v_h_3704_ = v___x_3742_;
v___y_3705_ = v___y_3726_;
v___y_3706_ = v___y_3727_;
v___y_3707_ = v___y_3728_;
v___y_3708_ = v___y_3729_;
v___y_3709_ = v___y_3730_;
v___y_3710_ = v___y_3731_;
v___y_3711_ = v___y_3732_;
v___y_3712_ = v___y_3733_;
v___y_3713_ = v___y_3734_;
v___y_3714_ = v___y_3735_;
v___y_3715_ = v___y_3736_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3670_, v_he_3671_);
v_h_3704_ = v___x_3743_;
v___y_3705_ = v___y_3726_;
v___y_3706_ = v___y_3727_;
v___y_3707_ = v___y_3728_;
v___y_3708_ = v___y_3729_;
v___y_3709_ = v___y_3730_;
v___y_3710_ = v___y_3731_;
v___y_3711_ = v___y_3732_;
v___y_3712_ = v___y_3733_;
v___y_3713_ = v___y_3734_;
v___y_3714_ = v___y_3735_;
v___y_3715_ = v___y_3736_;
goto v___jp_3703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3762_, lean_object* v_e_3763_, lean_object* v_he_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3762_, v_e_3763_, v_he_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec(v_a_3765_);
return v_res_3777_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_box(0);
v___x_3785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3786_ = l_Lean_mkConst(v___x_3785_, v___x_3784_);
return v___x_3786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_to_int(v___x_3787_);
return v___x_3788_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = lean_nat_to_int(v___x_3789_);
return v___x_3790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = lean_unsigned_to_nat(0u);
v___x_3797_ = l_Lean_Level_ofNat(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = lean_box(0);
v___x_3799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v___x_3798_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3803_ = l_Lean_Expr_const___override(v___x_3802_, v___x_3801_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_box(0);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3809_ = l_Lean_Expr_const___override(v___x_3808_, v___x_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = lean_box(0);
v___x_3815_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3816_ = l_Lean_Expr_const___override(v___x_3815_, v___x_3814_);
return v___x_3816_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3853_ = lean_box(0);
v___x_3854_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3855_ = l_Lean_mkConst(v___x_3854_, v___x_3853_);
return v___x_3855_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3858_ = l_Lean_stringToMessageData(v___x_3857_);
return v___x_3858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3859_, lean_object* v_e_3860_, lean_object* v_he_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v_k_x27_3877_; lean_object* v_h_3878_; uint8_t v_strict_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; uint8_t v___y_3935_; lean_object* v___x_3981_; 
v___x_3981_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4304_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_4304_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4304_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; uint8_t v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4013_; lean_object* v___y_4014_; uint8_t v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v_h_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; uint8_t v___x_4279_; 
v___x_4279_ = lean_unbox(v_a_3982_);
if (v___x_4279_ == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4282_; 
lean_dec(v_a_3982_);
lean_dec_ref(v_he_3861_);
lean_dec_ref(v_e_3860_);
lean_dec_ref(v_c_3859_);
v___x_4280_ = lean_box(0);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_4280_);
v___x_4282_ = v___x_3984_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
else
{
lean_object* v_toCold_4284_; lean_object* v_options_4285_; uint8_t v_hasTrace_4286_; 
lean_del_object(v___x_3984_);
v_toCold_4284_ = lean_ctor_get(v_a_3871_, 0);
v_options_4285_ = lean_ctor_get(v_toCold_4284_, 2);
v_hasTrace_4286_ = lean_ctor_get_uint8(v_options_4285_, sizeof(void*)*1);
if (v_hasTrace_4286_ == 0)
{
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
v___y_4266_ = v_a_3867_;
v___y_4267_ = v_a_3868_;
v___y_4268_ = v_a_3869_;
v___y_4269_ = v_a_3870_;
v___y_4270_ = v_a_3871_;
v___y_4271_ = v_a_3872_;
goto v___jp_4260_;
}
else
{
lean_object* v_inheritedTraceOptions_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; uint8_t v___x_4290_; 
v_inheritedTraceOptions_4287_ = lean_ctor_get(v_toCold_4284_, 11);
v___x_4288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4290_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4287_, v_options_4285_, v___x_4289_);
if (v___x_4290_ == 0)
{
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
v___y_4266_ = v_a_3867_;
v___y_4267_ = v_a_3868_;
v___y_4268_ = v_a_3869_;
v___y_4269_ = v_a_3870_;
v___y_4270_ = v_a_3871_;
v___y_4271_ = v_a_3872_;
goto v___jp_4260_;
}
else
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3859_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
v___x_4293_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4293_);
lean_ctor_set(v___x_4294_, 1, v_a_4292_);
v___x_4295_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4288_, v___x_4294_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_dec_ref_known(v___x_4295_, 1);
v___y_4261_ = v_a_3862_;
v___y_4262_ = v_a_3863_;
v___y_4263_ = v_a_3864_;
v___y_4264_ = v_a_3865_;
v___y_4265_ = v_a_3866_;
v___y_4266_ = v_a_3867_;
v___y_4267_ = v_a_3868_;
v___y_4268_ = v_a_3869_;
v___y_4269_ = v_a_3870_;
v___y_4270_ = v_a_3871_;
v___y_4271_ = v_a_3872_;
goto v___jp_4260_;
}
else
{
lean_dec(v_a_3982_);
lean_dec_ref(v_he_3861_);
lean_dec_ref(v_e_3860_);
lean_dec_ref(v_c_3859_);
return v___x_4295_;
}
}
else
{
lean_object* v_a_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4303_; 
lean_dec(v_a_3982_);
lean_dec_ref(v_he_3861_);
lean_dec_ref(v_e_3860_);
lean_dec_ref(v_c_3859_);
v_a_4296_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4298_ = v___x_4291_;
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_a_4296_);
lean_dec(v___x_4291_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4303_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4301_; 
if (v_isShared_4299_ == 0)
{
v___x_4301_ = v___x_4298_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
v___x_4301_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
return v___x_4301_;
}
}
}
}
}
}
v___jp_3986_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_4007_);
v___x_4009_ = l_Lean_mkApp6(v___y_4001_, v___y_3993_, v___y_3996_, v___y_3987_, v___y_4007_, v___x_4008_, v___y_3994_);
if (v___y_3990_ == 0)
{
uint8_t v___x_4010_; 
v___x_4010_ = lean_unbox(v_a_3982_);
lean_dec(v_a_3982_);
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3989_;
v___y_3920_ = v___y_3991_;
v___y_3921_ = v___y_3992_;
v___y_3922_ = v___y_3995_;
v___y_3923_ = v___x_4008_;
v___y_3924_ = v___x_4009_;
v___y_3925_ = v___y_3997_;
v___y_3926_ = v___y_3998_;
v___y_3927_ = v___y_3999_;
v___y_3928_ = v___y_4000_;
v___y_3929_ = v___y_4002_;
v___y_3930_ = v___y_4004_;
v___y_3931_ = v___y_4003_;
v___y_3932_ = v___y_4005_;
v___y_3933_ = v___y_4006_;
v___y_3934_ = v___y_4007_;
v___y_3935_ = v___x_4010_;
goto v___jp_3917_;
}
else
{
uint8_t v___x_4011_; 
lean_dec(v_a_3982_);
v___x_4011_ = 0;
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3989_;
v___y_3920_ = v___y_3991_;
v___y_3921_ = v___y_3992_;
v___y_3922_ = v___y_3995_;
v___y_3923_ = v___x_4008_;
v___y_3924_ = v___x_4009_;
v___y_3925_ = v___y_3997_;
v___y_3926_ = v___y_3998_;
v___y_3927_ = v___y_3999_;
v___y_3928_ = v___y_4000_;
v___y_3929_ = v___y_4002_;
v___y_3930_ = v___y_4004_;
v___y_3931_ = v___y_4003_;
v___y_3932_ = v___y_4005_;
v___y_3933_ = v___y_4006_;
v___y_3934_ = v___y_4007_;
v___y_3935_ = v___x_4011_;
goto v___jp_3917_;
}
}
v___jp_4012_:
{
lean_object* v___x_4033_; uint8_t v___x_4034_; 
v___x_4033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4034_ = lean_int_dec_le(v___x_4033_, v___y_4029_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4038_ = lean_int_neg(v___y_4029_);
v___x_4039_ = l_Int_toNat(v___x_4038_);
lean_dec(v___x_4038_);
v___x_4040_ = l_Lean_instToExprInt_mkNat(v___x_4039_);
v___x_4041_ = l_Lean_mkApp3(v___x_4035_, v___x_4036_, v___x_4037_, v___x_4040_);
v___y_3987_ = v___y_4032_;
v___y_3988_ = v___y_4013_;
v___y_3989_ = v___y_4014_;
v___y_3990_ = v___y_4015_;
v___y_3991_ = v___y_4016_;
v___y_3992_ = v___y_4017_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4019_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4021_;
v___y_3997_ = v___y_4022_;
v___y_3998_ = v___y_4023_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4027_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4028_;
v___y_4005_ = v___y_4030_;
v___y_4006_ = v___y_4031_;
v___y_4007_ = v___x_4041_;
goto v___jp_3986_;
}
else
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = l_Int_toNat(v___y_4029_);
v___x_4043_ = l_Lean_instToExprInt_mkNat(v___x_4042_);
v___y_3987_ = v___y_4032_;
v___y_3988_ = v___y_4013_;
v___y_3989_ = v___y_4014_;
v___y_3990_ = v___y_4015_;
v___y_3991_ = v___y_4016_;
v___y_3992_ = v___y_4017_;
v___y_3993_ = v___y_4018_;
v___y_3994_ = v___y_4019_;
v___y_3995_ = v___y_4020_;
v___y_3996_ = v___y_4021_;
v___y_3997_ = v___y_4022_;
v___y_3998_ = v___y_4023_;
v___y_3999_ = v___y_4024_;
v___y_4000_ = v___y_4025_;
v___y_4001_ = v___y_4026_;
v___y_4002_ = v___y_4027_;
v___y_4003_ = v___y_4029_;
v___y_4004_ = v___y_4028_;
v___y_4005_ = v___y_4030_;
v___y_4006_ = v___y_4031_;
v___y_4007_ = v___x_4043_;
goto v___jp_3986_;
}
}
v___jp_4044_:
{
lean_object* v___x_4062_; 
lean_inc(v___y_4061_);
v___x_4062_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4061_, v___y_4049_, v___y_4060_, v___y_4057_, v___y_4052_, v___y_4051_, v___y_4058_, v___y_4045_, v___y_4048_, v___y_4046_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___x_4062_, 1);
v___x_4064_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4059_, v___y_4049_, v___y_4060_, v___y_4057_, v___y_4052_, v___y_4051_, v___y_4058_, v___y_4045_, v___y_4048_, v___y_4046_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4066_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4053_, v___y_4049_, v___y_4060_, v___y_4057_, v___y_4052_, v___y_4051_, v___y_4058_, v___y_4045_, v___y_4048_, v___y_4046_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = lean_int_neg(v___y_4054_);
v___x_4069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4070_ = lean_int_dec_le(v___x_4069_, v___y_4054_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
lean_dec(v___y_4054_);
v___x_4071_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4072_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4074_ = l_Int_toNat(v___x_4068_);
v___x_4075_ = l_Lean_instToExprInt_mkNat(v___x_4074_);
v___x_4076_ = l_Lean_mkApp3(v___x_4071_, v___x_4072_, v___x_4073_, v___x_4075_);
v___y_4013_ = v___y_4045_;
v___y_4014_ = v___y_4046_;
v___y_4015_ = v___y_4047_;
v___y_4016_ = v___y_4048_;
v___y_4017_ = v___y_4049_;
v___y_4018_ = v_a_4065_;
v___y_4019_ = v___y_4050_;
v___y_4020_ = v___y_4051_;
v___y_4021_ = v_a_4067_;
v___y_4022_ = v___y_4052_;
v___y_4023_ = v___y_4053_;
v___y_4024_ = v___y_4055_;
v___y_4025_ = v___y_4056_;
v___y_4026_ = v_a_4063_;
v___y_4027_ = v___y_4057_;
v___y_4028_ = v___y_4058_;
v___y_4029_ = v___x_4068_;
v___y_4030_ = v___y_4059_;
v___y_4031_ = v___y_4060_;
v___y_4032_ = v___x_4076_;
goto v___jp_4012_;
}
else
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = l_Int_toNat(v___y_4054_);
lean_dec(v___y_4054_);
v___x_4078_ = l_Lean_instToExprInt_mkNat(v___x_4077_);
v___y_4013_ = v___y_4045_;
v___y_4014_ = v___y_4046_;
v___y_4015_ = v___y_4047_;
v___y_4016_ = v___y_4048_;
v___y_4017_ = v___y_4049_;
v___y_4018_ = v_a_4065_;
v___y_4019_ = v___y_4050_;
v___y_4020_ = v___y_4051_;
v___y_4021_ = v_a_4067_;
v___y_4022_ = v___y_4052_;
v___y_4023_ = v___y_4053_;
v___y_4024_ = v___y_4055_;
v___y_4025_ = v___y_4056_;
v___y_4026_ = v_a_4063_;
v___y_4027_ = v___y_4057_;
v___y_4028_ = v___y_4058_;
v___y_4029_ = v___x_4068_;
v___y_4030_ = v___y_4059_;
v___y_4031_ = v___y_4060_;
v___y_4032_ = v___x_4078_;
goto v___jp_4012_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_a_4065_);
lean_dec(v_a_4063_);
lean_dec(v___y_4059_);
lean_dec(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec(v_a_3982_);
v_a_4079_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4066_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4066_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_a_4063_);
lean_dec(v___y_4059_);
lean_dec(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec(v_a_3982_);
v_a_4087_ = lean_ctor_get(v___x_4064_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4064_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4064_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4064_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v___y_4059_);
lean_dec(v___y_4054_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4050_);
lean_dec(v_a_3982_);
v_a_4095_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4062_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4062_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
v___jp_4103_:
{
lean_object* v___x_4116_; 
v___x_4116_ = l_Lean_Meta_Grind_Order_isRing(v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; uint8_t v___x_4118_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref_known(v___x_4116_, 1);
v___x_4118_ = lean_unbox(v_a_4117_);
if (v___x_4118_ == 0)
{
uint8_t v_kind_4119_; 
v_kind_4119_ = lean_ctor_get_uint8(v_c_3859_, sizeof(void*)*5);
if (v_kind_4119_ == 1)
{
lean_object* v_u_4120_; lean_object* v_v_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
lean_dec(v_a_3982_);
v_u_4120_ = lean_ctor_get(v_c_3859_, 0);
lean_inc(v_u_4120_);
v_v_4121_ = lean_ctor_get(v_c_3859_, 1);
lean_inc(v_v_4121_);
lean_dec_ref(v_c_3859_);
v___x_4122_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4123_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4122_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4123_) == 0)
{
lean_object* v_a_4124_; lean_object* v___x_4125_; 
v_a_4124_ = lean_ctor_get(v___x_4123_, 0);
lean_inc(v_a_4124_);
lean_dec_ref_known(v___x_4123_, 1);
v___x_4125_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4120_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4121_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4133_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = l_Lean_mkApp3(v_a_4124_, v_a_4126_, v_a_4128_, v_h_4104_);
v___x_4130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4131_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
v___x_4132_ = lean_unbox(v_a_4117_);
lean_dec(v_a_4117_);
lean_ctor_set_uint8(v___x_4131_, sizeof(void*)*1, v___x_4132_);
v___x_4133_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4121_, v_u_4120_, v___x_4131_, v___x_4129_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4133_;
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec(v_a_4126_);
lean_dec(v_a_4124_);
lean_dec(v_v_4121_);
lean_dec(v_u_4120_);
lean_dec(v_a_4117_);
lean_dec_ref(v_h_4104_);
v_a_4134_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4127_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4127_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_a_4124_);
lean_dec(v_v_4121_);
lean_dec(v_u_4120_);
lean_dec(v_a_4117_);
lean_dec_ref(v_h_4104_);
v_a_4142_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4125_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4125_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_dec(v_v_4121_);
lean_dec(v_u_4120_);
lean_dec(v_a_4117_);
lean_dec_ref(v_h_4104_);
v_a_4150_ = lean_ctor_get(v___x_4123_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4123_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4123_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4123_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_u_4158_; lean_object* v_v_4159_; lean_object* v___x_4160_; 
lean_dec(v_a_4117_);
v_u_4158_ = lean_ctor_get(v_c_3859_, 0);
lean_inc(v_u_4158_);
v_v_4159_ = lean_ctor_get(v_c_3859_, 1);
lean_inc(v_v_4159_);
lean_dec_ref(v_c_3859_);
v___x_4160_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; uint8_t v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = lean_unbox(v_a_4161_);
if (v___x_4162_ == 0)
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec(v_a_3982_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4164_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4163_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4158_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4159_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = l_Lean_mkApp3(v_a_4165_, v_a_4167_, v_a_4169_, v_h_4104_);
v___x_4171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
v___x_4173_ = lean_unbox(v_a_4161_);
lean_dec(v_a_4161_);
lean_ctor_set_uint8(v___x_4172_, sizeof(void*)*1, v___x_4173_);
v___x_4174_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4159_, v_u_4158_, v___x_4172_, v___x_4170_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4174_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4167_);
lean_dec(v_a_4165_);
lean_dec(v_a_4161_);
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
v_a_4175_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4168_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4168_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v_a_4165_);
lean_dec(v_a_4161_);
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
v_a_4183_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4166_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4166_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_dec(v_a_4161_);
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
v_a_4191_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4164_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4164_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
else
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_dec(v_a_4161_);
v___x_4199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4200_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4199_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4158_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4159_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; lean_object* v___x_4210_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = l_Lean_mkApp3(v_a_4201_, v_a_4203_, v_a_4205_, v_h_4104_);
v___x_4207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
v___x_4209_ = lean_unbox(v_a_3982_);
lean_dec(v_a_3982_);
lean_ctor_set_uint8(v___x_4208_, sizeof(void*)*1, v___x_4209_);
v___x_4210_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4159_, v_u_4158_, v___x_4208_, v___x_4206_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4210_;
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec(v_a_4203_);
lean_dec(v_a_4201_);
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
lean_dec(v_a_3982_);
v_a_4211_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4204_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4204_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_dec(v_a_4201_);
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
lean_dec(v_a_3982_);
v_a_4219_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4202_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4202_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
lean_dec(v_a_3982_);
v_a_4227_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4200_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4200_);
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
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_v_4159_);
lean_dec(v_u_4158_);
lean_dec_ref(v_h_4104_);
lean_dec(v_a_3982_);
v_a_4235_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4160_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4160_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
else
{
uint8_t v_kind_4243_; 
lean_dec(v_a_4117_);
v_kind_4243_ = lean_ctor_get_uint8(v_c_3859_, sizeof(void*)*5);
if (v_kind_4243_ == 1)
{
lean_object* v_u_4244_; lean_object* v_v_4245_; lean_object* v_k_4246_; lean_object* v___x_4247_; 
v_u_4244_ = lean_ctor_get(v_c_3859_, 0);
lean_inc(v_u_4244_);
v_v_4245_ = lean_ctor_get(v_c_3859_, 1);
lean_inc(v_v_4245_);
v_k_4246_ = lean_ctor_get(v_c_3859_, 2);
lean_inc(v_k_4246_);
lean_dec_ref(v_c_3859_);
v___x_4247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4045_ = v___y_4111_;
v___y_4046_ = v___y_4113_;
v___y_4047_ = v_kind_4243_;
v___y_4048_ = v___y_4112_;
v___y_4049_ = v___y_4105_;
v___y_4050_ = v_h_4104_;
v___y_4051_ = v___y_4109_;
v___y_4052_ = v___y_4108_;
v___y_4053_ = v_v_4245_;
v___y_4054_ = v_k_4246_;
v___y_4055_ = v___y_4114_;
v___y_4056_ = v___y_4115_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___y_4110_;
v___y_4059_ = v_u_4244_;
v___y_4060_ = v___y_4106_;
v___y_4061_ = v___x_4247_;
goto v___jp_4044_;
}
else
{
lean_object* v_u_4248_; lean_object* v_v_4249_; lean_object* v_k_4250_; lean_object* v___x_4251_; 
v_u_4248_ = lean_ctor_get(v_c_3859_, 0);
lean_inc(v_u_4248_);
v_v_4249_ = lean_ctor_get(v_c_3859_, 1);
lean_inc(v_v_4249_);
v_k_4250_ = lean_ctor_get(v_c_3859_, 2);
lean_inc(v_k_4250_);
lean_dec_ref(v_c_3859_);
v___x_4251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4045_ = v___y_4111_;
v___y_4046_ = v___y_4113_;
v___y_4047_ = v_kind_4243_;
v___y_4048_ = v___y_4112_;
v___y_4049_ = v___y_4105_;
v___y_4050_ = v_h_4104_;
v___y_4051_ = v___y_4109_;
v___y_4052_ = v___y_4108_;
v___y_4053_ = v_v_4249_;
v___y_4054_ = v_k_4250_;
v___y_4055_ = v___y_4114_;
v___y_4056_ = v___y_4115_;
v___y_4057_ = v___y_4107_;
v___y_4058_ = v___y_4110_;
v___y_4059_ = v_u_4248_;
v___y_4060_ = v___y_4106_;
v___y_4061_ = v___x_4251_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec_ref(v_h_4104_);
lean_dec(v_a_3982_);
lean_dec_ref(v_c_3859_);
v_a_4252_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4116_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4116_);
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
v___jp_4260_:
{
lean_object* v_h_x3f_4272_; 
v_h_x3f_4272_ = lean_ctor_get(v_c_3859_, 4);
if (lean_obj_tag(v_h_x3f_4272_) == 1)
{
lean_object* v_e_4273_; lean_object* v_val_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_e_4273_ = lean_ctor_get(v_c_3859_, 3);
v_val_4274_ = lean_ctor_get(v_h_x3f_4272_, 0);
v___x_4275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3860_);
v___x_4276_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3860_, v_he_3861_);
lean_inc(v_val_4274_);
lean_inc_ref(v_e_4273_);
v___x_4277_ = l_Lean_mkApp4(v___x_4275_, v_e_3860_, v_e_4273_, v_val_4274_, v___x_4276_);
v_h_4104_ = v___x_4277_;
v___y_4105_ = v___y_4261_;
v___y_4106_ = v___y_4262_;
v___y_4107_ = v___y_4263_;
v___y_4108_ = v___y_4264_;
v___y_4109_ = v___y_4265_;
v___y_4110_ = v___y_4266_;
v___y_4111_ = v___y_4267_;
v___y_4112_ = v___y_4268_;
v___y_4113_ = v___y_4269_;
v___y_4114_ = v___y_4270_;
v___y_4115_ = v___y_4271_;
goto v___jp_4103_;
}
else
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3860_, v_he_3861_);
v_h_4104_ = v___x_4278_;
v___y_4105_ = v___y_4261_;
v___y_4106_ = v___y_4262_;
v___y_4107_ = v___y_4263_;
v___y_4108_ = v___y_4264_;
v___y_4109_ = v___y_4265_;
v___y_4110_ = v___y_4266_;
v___y_4111_ = v___y_4267_;
v___y_4112_ = v___y_4268_;
v___y_4113_ = v___y_4269_;
v___y_4114_ = v___y_4270_;
v___y_4115_ = v___y_4271_;
goto v___jp_4103_;
}
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref(v_he_3861_);
lean_dec_ref(v_e_3860_);
lean_dec_ref(v_c_3859_);
v_a_4305_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_3981_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_3981_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
v___jp_3874_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3891_, 0, v_k_x27_3877_);
lean_ctor_set_uint8(v___x_3891_, sizeof(void*)*1, v_strict_3879_);
v___x_3892_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3876_, v___y_3875_, v___x_3891_, v_h_3878_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
return v___x_3892_;
}
v___jp_3893_:
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
lean_inc_ref(v___y_3908_);
v___x_3915_ = l_Lean_mkApp6(v___y_3908_, v___y_3907_, v___y_3906_, v___y_3913_, v___y_3914_, v___y_3899_, v___y_3900_);
v___x_3916_ = 0;
v___y_3875_ = v___y_3911_;
v___y_3876_ = v___y_3903_;
v_k_x27_3877_ = v___y_3901_;
v_h_3878_ = v___x_3915_;
v_strict_3879_ = v___x_3916_;
v___y_3880_ = v___y_3897_;
v___y_3881_ = v___y_3912_;
v___y_3882_ = v___y_3909_;
v___y_3883_ = v___y_3902_;
v___y_3884_ = v___y_3898_;
v___y_3885_ = v___y_3910_;
v___y_3886_ = v___y_3895_;
v___y_3887_ = v___y_3896_;
v___y_3888_ = v___y_3894_;
v___y_3889_ = v___y_3904_;
v___y_3890_ = v___y_3905_;
goto v___jp_3874_;
}
v___jp_3917_:
{
lean_object* v___x_3936_; 
v___x_3936_ = l_Lean_Meta_Grind_Order_isInt(v___y_3921_, v___y_3933_, v___y_3929_, v___y_3925_, v___y_3922_, v___y_3930_, v___y_3918_, v___y_3920_, v___y_3919_, v___y_3927_, v___y_3928_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; uint8_t v___x_3938_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref_known(v___x_3936_, 1);
v___x_3938_ = lean_unbox(v_a_3937_);
lean_dec(v_a_3937_);
if (v___x_3938_ == 0)
{
lean_dec_ref(v___y_3934_);
lean_dec_ref(v___y_3923_);
v___y_3875_ = v___y_3932_;
v___y_3876_ = v___y_3926_;
v_k_x27_3877_ = v___y_3931_;
v_h_3878_ = v___y_3924_;
v_strict_3879_ = v___y_3935_;
v___y_3880_ = v___y_3921_;
v___y_3881_ = v___y_3933_;
v___y_3882_ = v___y_3929_;
v___y_3883_ = v___y_3925_;
v___y_3884_ = v___y_3922_;
v___y_3885_ = v___y_3930_;
v___y_3886_ = v___y_3918_;
v___y_3887_ = v___y_3920_;
v___y_3888_ = v___y_3919_;
v___y_3889_ = v___y_3927_;
v___y_3890_ = v___y_3928_;
goto v___jp_3874_;
}
else
{
if (v___y_3935_ == 0)
{
lean_dec_ref(v___y_3934_);
lean_dec_ref(v___y_3923_);
v___y_3875_ = v___y_3932_;
v___y_3876_ = v___y_3926_;
v_k_x27_3877_ = v___y_3931_;
v_h_3878_ = v___y_3924_;
v_strict_3879_ = v___y_3935_;
v___y_3880_ = v___y_3921_;
v___y_3881_ = v___y_3933_;
v___y_3882_ = v___y_3929_;
v___y_3883_ = v___y_3925_;
v___y_3884_ = v___y_3922_;
v___y_3885_ = v___y_3930_;
v___y_3886_ = v___y_3918_;
v___y_3887_ = v___y_3920_;
v___y_3888_ = v___y_3919_;
v___y_3889_ = v___y_3927_;
v___y_3890_ = v___y_3928_;
goto v___jp_3874_;
}
else
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3926_, v___y_3921_, v___y_3933_, v___y_3929_, v___y_3925_, v___y_3922_, v___y_3930_, v___y_3918_, v___y_3920_, v___y_3919_, v___y_3927_, v___y_3928_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3941_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v___x_3941_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3932_, v___y_3921_, v___y_3933_, v___y_3929_, v___y_3925_, v___y_3922_, v___y_3930_, v___y_3918_, v___y_3920_, v___y_3919_, v___y_3927_, v___y_3928_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
v___x_3943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3945_ = lean_int_sub(v___y_3931_, v___x_3944_);
lean_dec(v___y_3931_);
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3947_ = lean_int_dec_le(v___x_3946_, v___x_3945_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3951_ = lean_int_neg(v___x_3945_);
v___x_3952_ = l_Int_toNat(v___x_3951_);
lean_dec(v___x_3951_);
v___x_3953_ = l_Lean_instToExprInt_mkNat(v___x_3952_);
v___x_3954_ = l_Lean_mkApp3(v___x_3948_, v___x_3949_, v___x_3950_, v___x_3953_);
v___y_3894_ = v___y_3919_;
v___y_3895_ = v___y_3918_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3921_;
v___y_3898_ = v___y_3922_;
v___y_3899_ = v___y_3923_;
v___y_3900_ = v___y_3924_;
v___y_3901_ = v___x_3945_;
v___y_3902_ = v___y_3925_;
v___y_3903_ = v___y_3926_;
v___y_3904_ = v___y_3927_;
v___y_3905_ = v___y_3928_;
v___y_3906_ = v_a_3942_;
v___y_3907_ = v_a_3940_;
v___y_3908_ = v___x_3943_;
v___y_3909_ = v___y_3929_;
v___y_3910_ = v___y_3930_;
v___y_3911_ = v___y_3932_;
v___y_3912_ = v___y_3933_;
v___y_3913_ = v___y_3934_;
v___y_3914_ = v___x_3954_;
goto v___jp_3893_;
}
else
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = l_Int_toNat(v___x_3945_);
v___x_3956_ = l_Lean_instToExprInt_mkNat(v___x_3955_);
v___y_3894_ = v___y_3919_;
v___y_3895_ = v___y_3918_;
v___y_3896_ = v___y_3920_;
v___y_3897_ = v___y_3921_;
v___y_3898_ = v___y_3922_;
v___y_3899_ = v___y_3923_;
v___y_3900_ = v___y_3924_;
v___y_3901_ = v___x_3945_;
v___y_3902_ = v___y_3925_;
v___y_3903_ = v___y_3926_;
v___y_3904_ = v___y_3927_;
v___y_3905_ = v___y_3928_;
v___y_3906_ = v_a_3942_;
v___y_3907_ = v_a_3940_;
v___y_3908_ = v___x_3943_;
v___y_3909_ = v___y_3929_;
v___y_3910_ = v___y_3930_;
v___y_3911_ = v___y_3932_;
v___y_3912_ = v___y_3933_;
v___y_3913_ = v___y_3934_;
v___y_3914_ = v___x_3956_;
goto v___jp_3893_;
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3940_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___y_3923_);
v_a_3957_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3941_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3941_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___y_3923_);
v_a_3965_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3939_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3939_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec(v___y_3926_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___y_3923_);
v_a_3973_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3936_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3936_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4313_, lean_object* v_e_4314_, lean_object* v_he_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_){
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4313_, v_e_4314_, v_he_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_);
lean_dec(v_a_4326_);
lean_dec_ref(v_a_4325_);
lean_dec(v_a_4324_);
lean_dec_ref(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
lean_dec(v_a_4320_);
lean_dec_ref(v_a_4319_);
lean_dec(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec(v_a_4316_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4330_, v_a_4331_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4343_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4336_ = v___x_4333_;
v_isShared_4337_ = v_isSharedCheck_4343_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_a_4334_);
lean_dec(v___x_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4343_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v_exprToStructId_4338_; lean_object* v___x_4339_; lean_object* v___x_4341_; 
v_exprToStructId_4338_ = lean_ctor_get(v_a_4334_, 2);
lean_inc_ref(v_exprToStructId_4338_);
lean_dec(v_a_4334_);
v___x_4339_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4338_, v_e_4329_);
lean_dec_ref(v_exprToStructId_4338_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 0, v___x_4339_);
v___x_4341_ = v___x_4336_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4339_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
v_a_4344_ = lean_ctor_get(v___x_4333_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4333_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v___x_4333_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4352_, v_a_4353_, v_a_4354_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_e_4352_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4357_, v_a_4358_, v_a_4366_);
return v___x_4369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_);
lean_dec(v_a_4380_);
lean_dec_ref(v_a_4379_);
lean_dec(v_a_4378_);
lean_dec_ref(v_a_4377_);
lean_dec(v_a_4376_);
lean_dec_ref(v_a_4375_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec(v_a_4371_);
lean_dec_ref(v_e_4370_);
return v_res_4382_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4389_ = lean_box(0);
v___x_4390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4391_ = l_Lean_mkConst(v___x_4390_, v___x_4389_);
return v___x_4391_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_box(0);
v___x_4399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4400_ = l_Lean_mkConst(v___x_4399_, v___x_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4401_, lean_object* v_e_x27_4402_, lean_object* v_he_x3f_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v___x_4415_; 
v___x_4415_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4402_, v_a_4404_, v_a_4412_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4506_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4506_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4506_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
if (lean_obj_tag(v_a_4416_) == 1)
{
lean_object* v_val_4420_; lean_object* v___x_4421_; 
lean_del_object(v___x_4418_);
v_val_4420_ = lean_ctor_get(v_a_4416_, 0);
lean_inc(v_val_4420_);
lean_dec_ref_known(v_a_4416_, 1);
v___x_4421_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_x27_4402_, v_val_4420_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4493_; 
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4493_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4493_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
if (lean_obj_tag(v_a_4422_) == 1)
{
lean_object* v_val_4426_; lean_object* v___x_4427_; 
lean_del_object(v___x_4424_);
v_val_4426_ = lean_ctor_get(v_a_4422_, 0);
lean_inc(v_val_4426_);
lean_dec_ref_known(v_a_4422_, 1);
lean_inc_ref(v_e_4401_);
v___x_4427_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4401_, v_a_4404_, v_a_4408_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4427_) == 0)
{
lean_object* v_a_4428_; uint8_t v___x_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref_known(v___x_4427_, 1);
v___x_4429_ = lean_unbox(v_a_4428_);
lean_dec(v_a_4428_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; 
lean_inc_ref(v_e_4401_);
v___x_4430_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4401_, v_a_4404_, v_a_4408_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4456_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4433_ = v___x_4430_;
v_isShared_4434_ = v_isSharedCheck_4456_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4456_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
uint8_t v___x_4435_; 
v___x_4435_ = lean_unbox(v_a_4431_);
lean_dec(v_a_4431_);
if (v___x_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
lean_dec(v_val_4426_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v___x_4436_ = lean_box(0);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4436_);
v___x_4438_ = v___x_4433_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
else
{
lean_object* v___x_4440_; 
lean_del_object(v___x_4433_);
lean_inc_ref(v_e_4401_);
v___x_4440_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4401_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4440_) == 0)
{
if (lean_obj_tag(v_he_x3f_4403_) == 1)
{
lean_object* v_a_4441_; lean_object* v_val_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v_val_4442_ = lean_ctor_get(v_he_x3f_4403_, 0);
lean_inc(v_val_4442_);
lean_dec_ref_known(v_he_x3f_4403_, 1);
v___x_4443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4402_);
v___x_4444_ = l_Lean_mkApp4(v___x_4443_, v_e_4401_, v_e_x27_4402_, v_val_4442_, v_a_4441_);
v___x_4445_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4426_, v_e_x27_4402_, v___x_4444_, v_val_4420_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_val_4420_);
return v___x_4445_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4447_; 
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_4401_);
v_a_4446_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4446_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4447_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4426_, v_e_x27_4402_, v_a_4446_, v_val_4420_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_val_4420_);
return v___x_4447_;
}
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_val_4426_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4448_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4440_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4440_);
v___x_4450_ = lean_box(0);
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
v_resetjp_4449_:
{
lean_object* v___x_4453_; 
if (v_isShared_4451_ == 0)
{
v___x_4453_ = v___x_4450_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
v___x_4453_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
return v___x_4453_;
}
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_val_4426_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4457_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4430_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4430_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
else
{
lean_object* v___x_4465_; 
lean_inc_ref(v_e_4401_);
v___x_4465_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4401_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4465_) == 0)
{
if (lean_obj_tag(v_he_x3f_4403_) == 1)
{
lean_object* v_a_4466_; lean_object* v_val_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v_val_4467_ = lean_ctor_get(v_he_x3f_4403_, 0);
lean_inc(v_val_4467_);
lean_dec_ref_known(v_he_x3f_4403_, 1);
v___x_4468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4402_);
v___x_4469_ = l_Lean_mkApp4(v___x_4468_, v_e_4401_, v_e_x27_4402_, v_val_4467_, v_a_4466_);
v___x_4470_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4426_, v_e_x27_4402_, v___x_4469_, v_val_4420_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_val_4420_);
return v___x_4470_;
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4472_; 
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_4401_);
v_a_4471_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v___x_4465_, 1);
v___x_4472_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4426_, v_e_x27_4402_, v_a_4471_, v_val_4420_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_val_4420_);
return v___x_4472_;
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v_val_4426_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4473_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4465_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4465_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_val_4426_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4481_ = lean_ctor_get(v___x_4427_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4427_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4427_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4427_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
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
lean_object* v___x_4489_; lean_object* v___x_4491_; 
lean_dec(v_a_4422_);
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v___x_4489_ = lean_box(0);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4489_);
v___x_4491_ = v___x_4424_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4489_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_val_4420_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4494_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4421_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4421_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_dec(v_a_4416_);
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v___x_4502_ = lean_box(0);
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v___x_4502_);
v___x_4504_ = v___x_4418_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_dec(v_he_x3f_4403_);
lean_dec_ref(v_e_x27_4402_);
lean_dec_ref(v_e_4401_);
v_a_4507_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4415_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4415_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4515_, lean_object* v_e_x27_4516_, lean_object* v_he_x3f_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v_res_4529_; 
v_res_4529_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4515_, v_e_x27_4516_, v_he_x3f_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec(v_a_4518_);
return v_res_4529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4531_, v_a_4539_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v_termMap_4544_; lean_object* v___x_4545_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4542_, 1);
v_termMap_4544_ = lean_ctor_get(v_a_4543_, 3);
lean_inc_ref(v_termMap_4544_);
lean_dec(v_a_4543_);
v___x_4545_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4544_, v_e_4530_);
lean_dec_ref(v_termMap_4544_);
if (lean_obj_tag(v___x_4545_) == 1)
{
lean_object* v_val_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4556_; 
v_val_4546_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4548_ = v___x_4545_;
v_isShared_4549_ = v_isSharedCheck_4556_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_val_4546_);
lean_dec(v___x_4545_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4556_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v_e_4550_; lean_object* v_h_4551_; lean_object* v___x_4553_; 
v_e_4550_ = lean_ctor_get(v_val_4546_, 0);
lean_inc_ref(v_e_4550_);
v_h_4551_ = lean_ctor_get(v_val_4546_, 1);
lean_inc_ref(v_h_4551_);
lean_dec(v_val_4546_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 0, v_h_4551_);
v___x_4553_ = v___x_4548_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_h_4551_);
v___x_4553_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; 
v___x_4554_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4530_, v_e_4550_, v___x_4553_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
return v___x_4554_;
}
}
}
else
{
lean_object* v___x_4557_; lean_object* v___x_4558_; 
lean_dec(v___x_4545_);
v___x_4557_ = lean_box(0);
lean_inc_ref(v_e_4530_);
v___x_4558_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4530_, v_e_4530_, v___x_4557_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
return v___x_4558_;
}
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec_ref(v_e_4530_);
v_a_4559_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4542_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4542_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
lean_dec(v_a_4577_);
lean_dec_ref(v_a_4576_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
lean_dec(v_a_4571_);
lean_dec_ref(v_a_4570_);
lean_dec(v_a_4569_);
lean_dec(v_a_4568_);
return v_res_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___x_4592_; 
v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec(v_a_4594_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___f_4613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4615_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4614_, v___f_4613_);
return v___x_4615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object* v_a_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_){
_start:
{
lean_object* v___x_4630_; 
v___x_4630_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_);
return v___x_4630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
lean_dec(v_a_4639_);
lean_dec_ref(v_a_4638_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec(v_a_4632_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; 
v___f_4650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_));
v___x_4652_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4651_, v___f_4650_);
return v___x_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object* v_a_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4656_, v_a_4657_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4669_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4669_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4669_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_termMap_4664_; lean_object* v___x_4665_; lean_object* v___x_4667_; 
v_termMap_4664_ = lean_ctor_get(v_a_4660_, 3);
lean_inc_ref(v_termMap_4664_);
lean_dec(v_a_4660_);
v___x_4665_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4664_, v_e_4655_);
lean_dec_ref(v_termMap_4664_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4665_);
v___x_4667_ = v___x_4662_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; uint8_t v_isShared_4673_; uint8_t v_isSharedCheck_4677_; 
v_a_4670_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4672_ = v___x_4659_;
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
else
{
lean_inc(v_a_4670_);
lean_dec(v___x_4659_);
v___x_4672_ = lean_box(0);
v_isShared_4673_ = v_isSharedCheck_4677_;
goto v_resetjp_4671_;
}
v_resetjp_4671_:
{
lean_object* v___x_4675_; 
if (v_isShared_4673_ == 0)
{
v___x_4675_ = v___x_4672_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_a_4670_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4678_, v_a_4679_, v_a_4680_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_e_4678_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_){
_start:
{
lean_object* v___x_4695_; 
v___x_4695_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4683_, v_a_4684_, v_a_4692_);
return v___x_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
lean_dec(v_a_4704_);
lean_dec_ref(v_a_4703_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
lean_dec(v_a_4698_);
lean_dec(v_a_4697_);
lean_dec_ref(v_e_4696_);
return v_res_4708_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; 
v___x_4733_ = 0;
v___x_4734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4735_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*1, v___x_4733_);
return v___x_4735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4738_ = l_Lean_stringToMessageData(v___x_4737_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4739_, lean_object* v_b_4740_, lean_object* v_h_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___x_4852_; 
v___x_4852_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4739_, v_a_4742_, v_a_4750_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4855_; uint8_t v_isShared_4856_; uint8_t v_isSharedCheck_4899_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4855_ = v___x_4852_;
v_isShared_4856_ = v_isSharedCheck_4899_;
goto v_resetjp_4854_;
}
else
{
lean_inc(v_a_4853_);
lean_dec(v___x_4852_);
v___x_4855_ = lean_box(0);
v_isShared_4856_ = v_isSharedCheck_4899_;
goto v_resetjp_4854_;
}
v_resetjp_4854_:
{
if (lean_obj_tag(v_a_4853_) == 1)
{
lean_object* v_val_4857_; lean_object* v___x_4858_; 
lean_del_object(v___x_4855_);
v_val_4857_ = lean_ctor_get(v_a_4853_, 0);
lean_inc(v_val_4857_);
lean_dec_ref_known(v_a_4853_, 1);
v___x_4858_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4740_, v_a_4742_, v_a_4750_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; lean_object* v___x_4861_; uint8_t v_isShared_4862_; uint8_t v_isSharedCheck_4886_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4861_ = v___x_4858_;
v_isShared_4862_ = v_isSharedCheck_4886_;
goto v_resetjp_4860_;
}
else
{
lean_inc(v_a_4859_);
lean_dec(v___x_4858_);
v___x_4861_ = lean_box(0);
v_isShared_4862_ = v_isSharedCheck_4886_;
goto v_resetjp_4860_;
}
v_resetjp_4860_:
{
if (lean_obj_tag(v_a_4859_) == 1)
{
lean_object* v_val_4863_; uint8_t v___x_4864_; 
v_val_4863_ = lean_ctor_get(v_a_4859_, 0);
lean_inc(v_val_4863_);
lean_dec_ref_known(v_a_4859_, 1);
v___x_4864_ = lean_nat_dec_eq(v_val_4857_, v_val_4863_);
lean_dec(v_val_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4867_; 
lean_dec(v_val_4857_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v___x_4865_ = lean_box(0);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 0, v___x_4865_);
v___x_4867_ = v___x_4861_;
goto v_reusejp_4866_;
}
else
{
lean_object* v_reuseFailAlloc_4868_; 
v_reuseFailAlloc_4868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4868_, 0, v___x_4865_);
v___x_4867_ = v_reuseFailAlloc_4868_;
goto v_reusejp_4866_;
}
v_reusejp_4866_:
{
return v___x_4867_;
}
}
else
{
lean_object* v_toCold_4869_; lean_object* v_options_4870_; uint8_t v_hasTrace_4871_; 
lean_del_object(v___x_4861_);
v_toCold_4869_ = lean_ctor_get(v_a_4750_, 0);
v_options_4870_ = lean_ctor_get(v_toCold_4869_, 2);
v_hasTrace_4871_ = lean_ctor_get_uint8(v_options_4870_, sizeof(void*)*1);
if (v_hasTrace_4871_ == 0)
{
v___y_4754_ = v_val_4857_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
v___y_4758_ = v_a_4745_;
v___y_4759_ = v_a_4746_;
v___y_4760_ = v_a_4747_;
v___y_4761_ = v_a_4748_;
v___y_4762_ = v_a_4749_;
v___y_4763_ = v_a_4750_;
v___y_4764_ = v_a_4751_;
goto v___jp_4753_;
}
else
{
lean_object* v_inheritedTraceOptions_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; uint8_t v___x_4875_; 
v_inheritedTraceOptions_4872_ = lean_ctor_get(v_toCold_4869_, 11);
v___x_4873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4874_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4872_, v_options_4870_, v___x_4874_);
if (v___x_4875_ == 0)
{
v___y_4754_ = v_val_4857_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
v___y_4758_ = v_a_4745_;
v___y_4759_ = v_a_4746_;
v___y_4760_ = v_a_4747_;
v___y_4761_ = v_a_4748_;
v___y_4762_ = v_a_4749_;
v___y_4763_ = v_a_4750_;
v___y_4764_ = v_a_4751_;
goto v___jp_4753_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
lean_inc_ref(v_a_4739_);
v___x_4876_ = l_Lean_MessageData_ofExpr(v_a_4739_);
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4876_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
lean_inc_ref(v_b_4740_);
v___x_4879_ = l_Lean_MessageData_ofExpr(v_b_4740_);
v___x_4880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4878_);
lean_ctor_set(v___x_4880_, 1, v___x_4879_);
v___x_4881_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4873_, v___x_4880_, v_a_4748_, v_a_4749_, v_a_4750_, v_a_4751_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_dec_ref_known(v___x_4881_, 1);
v___y_4754_ = v_val_4857_;
v___y_4755_ = v_a_4742_;
v___y_4756_ = v_a_4743_;
v___y_4757_ = v_a_4744_;
v___y_4758_ = v_a_4745_;
v___y_4759_ = v_a_4746_;
v___y_4760_ = v_a_4747_;
v___y_4761_ = v_a_4748_;
v___y_4762_ = v_a_4749_;
v___y_4763_ = v_a_4750_;
v___y_4764_ = v_a_4751_;
goto v___jp_4753_;
}
else
{
lean_dec(v_val_4857_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
return v___x_4881_;
}
}
}
}
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
lean_dec(v_a_4859_);
lean_dec(v_val_4857_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v___x_4882_ = lean_box(0);
if (v_isShared_4862_ == 0)
{
lean_ctor_set(v___x_4861_, 0, v___x_4882_);
v___x_4884_ = v___x_4861_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v___x_4882_);
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
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4894_; 
lean_dec(v_val_4857_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4887_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4858_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4858_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4892_; 
if (v_isShared_4890_ == 0)
{
v___x_4892_ = v___x_4889_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4893_; 
v_reuseFailAlloc_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4893_, 0, v_a_4887_);
v___x_4892_ = v_reuseFailAlloc_4893_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
return v___x_4892_;
}
}
}
}
else
{
lean_object* v___x_4895_; lean_object* v___x_4897_; 
lean_dec(v_a_4853_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v___x_4895_ = lean_box(0);
if (v_isShared_4856_ == 0)
{
lean_ctor_set(v___x_4855_, 0, v___x_4895_);
v___x_4897_ = v___x_4855_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4895_);
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
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4900_ = lean_ctor_get(v___x_4852_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4852_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4902_ = v___x_4852_;
v_isShared_4903_ = v_isSharedCheck_4907_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v___x_4852_);
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
v___jp_4753_:
{
lean_object* v___x_4765_; 
lean_inc_ref(v_a_4739_);
v___x_4765_ = l_Lean_Meta_Grind_Order_getNodeId(v_a_4739_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4765_) == 0)
{
lean_object* v_a_4766_; lean_object* v___x_4767_; 
v_a_4766_ = lean_ctor_get(v___x_4765_, 0);
lean_inc(v_a_4766_);
lean_dec_ref_known(v___x_4765_, 1);
lean_inc_ref(v_b_4740_);
v___x_4767_ = l_Lean_Meta_Grind_Order_getNodeId(v_b_4740_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4767_) == 0)
{
lean_object* v_a_4768_; lean_object* v___x_4769_; 
v_a_4768_ = lean_ctor_get(v___x_4767_, 0);
lean_inc(v_a_4768_);
lean_dec_ref_known(v___x_4767_, 1);
v___x_4769_ = l_Lean_Meta_Grind_Order_isRing(v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_object* v_a_4770_; uint8_t v___x_4771_; 
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
lean_inc(v_a_4770_);
lean_dec_ref_known(v___x_4769_, 1);
v___x_4771_ = lean_unbox(v_a_4770_);
if (v___x_4771_ == 0)
{
lean_object* v___x_4772_; lean_object* v___x_4773_; 
v___x_4772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4773_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4772_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4773_) == 0)
{
lean_object* v_a_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_a_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc(v_a_4774_);
lean_dec_ref_known(v___x_4773_, 1);
v___x_4775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4776_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4775_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_object* v_a_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; lean_object* v___x_4782_; 
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref_known(v___x_4776_, 1);
lean_inc_ref(v_h_4741_);
lean_inc_ref(v_b_4740_);
lean_inc_ref(v_a_4739_);
v___x_4778_ = l_Lean_mkApp3(v_a_4774_, v_a_4739_, v_b_4740_, v_h_4741_);
v___x_4779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4780_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
v___x_4781_ = lean_unbox(v_a_4770_);
lean_dec(v_a_4770_);
lean_ctor_set_uint8(v___x_4780_, sizeof(void*)*1, v___x_4781_);
lean_inc_ref(v___x_4780_);
lean_inc(v_a_4768_);
lean_inc(v_a_4766_);
v___x_4782_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4766_, v_a_4768_, v___x_4780_, v___x_4778_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
lean_dec_ref_known(v___x_4782_, 1);
v___x_4783_ = l_Lean_mkApp3(v_a_4777_, v_a_4739_, v_b_4740_, v_h_4741_);
v___x_4784_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4768_, v_a_4766_, v___x_4780_, v___x_4783_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4754_);
return v___x_4784_;
}
else
{
lean_dec_ref_known(v___x_4780_, 1);
lean_dec(v_a_4777_);
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
return v___x_4782_;
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec(v_a_4774_);
lean_dec(v_a_4770_);
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4785_ = lean_ctor_get(v___x_4776_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4776_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4776_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec(v_a_4770_);
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4793_ = lean_ctor_get(v___x_4773_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4773_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4773_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4773_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
else
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
lean_dec(v_a_4770_);
v___x_4801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4802_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4801_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref_known(v___x_4802_, 1);
v___x_4804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4805_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4804_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4805_, 1);
lean_inc_ref(v_h_4741_);
lean_inc_ref(v_b_4740_);
lean_inc_ref(v_a_4739_);
v___x_4807_ = l_Lean_mkApp3(v_a_4803_, v_a_4739_, v_b_4740_, v_h_4741_);
v___x_4808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4768_);
lean_inc(v_a_4766_);
v___x_4809_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4766_, v_a_4768_, v___x_4808_, v___x_4807_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
lean_dec_ref_known(v___x_4809_, 1);
v___x_4810_ = l_Lean_mkApp3(v_a_4806_, v_a_4739_, v_b_4740_, v_h_4741_);
v___x_4811_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4768_, v_a_4766_, v___x_4808_, v___x_4810_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4754_);
return v___x_4811_;
}
else
{
lean_dec(v_a_4806_);
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
return v___x_4809_;
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec(v_a_4803_);
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4812_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4805_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4805_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4820_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4802_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4802_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec(v_a_4768_);
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4828_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4769_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4769_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
lean_dec(v_a_4766_);
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4836_ = lean_ctor_get(v___x_4767_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4767_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4767_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4767_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4839_ == 0)
{
v___x_4841_ = v___x_4838_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
else
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec(v___y_4754_);
lean_dec_ref(v_h_4741_);
lean_dec_ref(v_b_4740_);
lean_dec_ref(v_a_4739_);
v_a_4844_ = lean_ctor_get(v___x_4765_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4765_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4765_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4908_, lean_object* v_b_4909_, lean_object* v_h_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4908_, v_b_4909_, v_h_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_);
lean_dec(v_a_4920_);
lean_dec_ref(v_a_4919_);
lean_dec(v_a_4918_);
lean_dec_ref(v_a_4917_);
lean_dec(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec(v_a_4914_);
lean_dec_ref(v_a_4913_);
lean_dec(v_a_4912_);
lean_dec(v_a_4911_);
return v_res_4922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4938_ = lean_box(0);
v___x_4939_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4940_ = l_Lean_mkConst(v___x_4939_, v___x_4938_);
return v___x_4940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4941_, lean_object* v_b_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_){
_start:
{
size_t v___x_4954_; size_t v___x_4955_; uint8_t v___x_4956_; 
v___x_4954_ = lean_ptr_addr(v_a_4941_);
v___x_4955_ = lean_ptr_addr(v_b_4942_);
v___x_4956_ = lean_usize_dec_eq(v___x_4954_, v___x_4955_);
if (v___x_4956_ == 0)
{
lean_object* v___x_4957_; 
lean_inc(v_a_4952_);
lean_inc_ref(v_a_4951_);
lean_inc(v_a_4950_);
lean_inc_ref(v_a_4949_);
lean_inc(v_a_4948_);
lean_inc_ref(v_a_4947_);
lean_inc(v_a_4946_);
lean_inc_ref(v_a_4945_);
lean_inc(v_a_4944_);
lean_inc(v_a_4943_);
lean_inc_ref(v_b_4942_);
lean_inc_ref(v_a_4941_);
v___x_4957_ = lean_grind_mk_eq_proof(v_a_4941_, v_b_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; lean_object* v___x_4959_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref_known(v___x_4957_, 1);
v___x_4959_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4941_, v_a_4943_, v_a_4951_);
if (lean_obj_tag(v___x_4959_) == 0)
{
lean_object* v_a_4960_; 
v_a_4960_ = lean_ctor_get(v___x_4959_, 0);
lean_inc(v_a_4960_);
lean_dec_ref_known(v___x_4959_, 1);
if (lean_obj_tag(v_a_4960_) == 1)
{
lean_object* v_val_4961_; lean_object* v_e_4962_; lean_object* v_h_4963_; lean_object* v_00_u03b1_4964_; lean_object* v___x_4965_; 
v_val_4961_ = lean_ctor_get(v_a_4960_, 0);
lean_inc(v_val_4961_);
lean_dec_ref_known(v_a_4960_, 1);
v_e_4962_ = lean_ctor_get(v_val_4961_, 0);
lean_inc_ref(v_e_4962_);
v_h_4963_ = lean_ctor_get(v_val_4961_, 1);
lean_inc_ref(v_h_4963_);
v_00_u03b1_4964_ = lean_ctor_get(v_val_4961_, 2);
lean_inc_ref(v_00_u03b1_4964_);
lean_dec(v_val_4961_);
v___x_4965_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4942_, v_a_4943_, v_a_4951_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5011_; 
v_a_4966_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_4968_ = v___x_4965_;
v_isShared_4969_ = v_isSharedCheck_5011_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4965_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5011_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
if (lean_obj_tag(v_a_4966_) == 1)
{
lean_object* v_val_4970_; lean_object* v_e_4971_; lean_object* v_h_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; 
lean_del_object(v___x_4968_);
v_val_4970_ = lean_ctor_get(v_a_4966_, 0);
lean_inc(v_val_4970_);
lean_dec_ref_known(v_a_4966_, 1);
v_e_4971_ = lean_ctor_get(v_val_4970_, 0);
lean_inc_ref(v_e_4971_);
v_h_4972_ = lean_ctor_get(v_val_4970_, 1);
lean_inc_ref(v_h_4972_);
lean_dec(v_val_4970_);
v___x_4973_ = l_Lean_Int_mkType;
v___x_4974_ = lean_expr_eqv(v_00_u03b1_4964_, v___x_4973_);
if (v___x_4974_ == 0)
{
lean_object* v___x_4975_; 
lean_inc_ref(v_00_u03b1_4964_);
v___x_4975_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4964_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4975_) == 0)
{
lean_object* v_a_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_a_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_a_4976_);
lean_dec_ref_known(v___x_4975_, 1);
v___x_4977_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4978_ = lean_box(0);
v___x_4979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4979_, 0, v_a_4976_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
lean_inc_ref(v___x_4979_);
v___x_4980_ = l_Lean_mkConst(v___x_4977_, v___x_4979_);
lean_inc_ref(v_00_u03b1_4964_);
v___x_4981_ = l_Lean_Expr_app___override(v___x_4980_, v_00_u03b1_4964_);
v___x_4982_ = l_Lean_Meta_Sym_synthInstance(v___x_4981_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
v___x_4984_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_4985_ = l_Lean_mkConst(v___x_4984_, v___x_4979_);
lean_inc_ref(v_e_4971_);
lean_inc_ref(v_e_4962_);
v___x_4986_ = l_Lean_mkApp9(v___x_4985_, v_00_u03b1_4964_, v_a_4983_, v_a_4941_, v_b_4942_, v_e_4962_, v_e_4971_, v_h_4963_, v_h_4972_, v_a_4958_);
v___x_4987_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4962_, v_e_4971_, v___x_4986_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_4987_;
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_dec_ref_known(v___x_4979_, 2);
lean_dec_ref(v_h_4972_);
lean_dec_ref(v_e_4971_);
lean_dec_ref(v_00_u03b1_4964_);
lean_dec_ref(v_h_4963_);
lean_dec_ref(v_e_4962_);
lean_dec(v_a_4958_);
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v_a_4988_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4982_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4982_);
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
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec_ref(v_h_4972_);
lean_dec_ref(v_e_4971_);
lean_dec_ref(v_00_u03b1_4964_);
lean_dec_ref(v_h_4963_);
lean_dec_ref(v_e_4962_);
lean_dec(v_a_4958_);
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v_a_4996_ = lean_ctor_get(v___x_4975_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4975_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4975_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4975_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
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
lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_dec_ref(v_00_u03b1_4964_);
v___x_5004_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_4971_);
lean_inc_ref(v_e_4962_);
v___x_5005_ = l_Lean_mkApp7(v___x_5004_, v_a_4941_, v_b_4942_, v_e_4962_, v_e_4971_, v_h_4963_, v_h_4972_, v_a_4958_);
v___x_5006_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4962_, v_e_4971_, v___x_5005_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_5006_;
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5009_; 
lean_dec(v_a_4966_);
lean_dec_ref(v_00_u03b1_4964_);
lean_dec_ref(v_h_4963_);
lean_dec_ref(v_e_4962_);
lean_dec(v_a_4958_);
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v___x_5007_ = lean_box(0);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v___x_5007_);
v___x_5009_ = v___x_4968_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v___x_5007_);
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
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
lean_dec_ref(v_00_u03b1_4964_);
lean_dec_ref(v_h_4963_);
lean_dec_ref(v_e_4962_);
lean_dec(v_a_4958_);
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v_a_5012_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_4965_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_4965_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
}
else
{
lean_object* v___x_5020_; 
lean_dec(v_a_4960_);
v___x_5020_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4941_, v_b_4942_, v_a_4958_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_, v_a_4950_, v_a_4951_, v_a_4952_);
return v___x_5020_;
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
lean_dec(v_a_4958_);
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v_a_5021_ = lean_ctor_get(v___x_4959_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_4959_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_4959_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_4959_);
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
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v_a_5029_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_4957_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_4957_);
v___x_5031_ = lean_box(0);
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
v_resetjp_5030_:
{
lean_object* v___x_5034_; 
if (v_isShared_5032_ == 0)
{
v___x_5034_ = v___x_5031_;
goto v_reusejp_5033_;
}
else
{
lean_object* v_reuseFailAlloc_5035_; 
v_reuseFailAlloc_5035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
v___x_5034_ = v_reuseFailAlloc_5035_;
goto v_reusejp_5033_;
}
v_reusejp_5033_:
{
return v___x_5034_;
}
}
}
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v_b_4942_);
lean_dec_ref(v_a_4941_);
v___x_5037_ = lean_box(0);
v___x_5038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5037_);
return v___x_5038_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5039_, lean_object* v_b_5040_, lean_object* v_a_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_, lean_object* v_a_5044_, lean_object* v_a_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_, lean_object* v_a_5051_){
_start:
{
lean_object* v_res_5052_; 
v_res_5052_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5039_, v_b_5040_, v_a_5041_, v_a_5042_, v_a_5043_, v_a_5044_, v_a_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
lean_dec(v_a_5050_);
lean_dec_ref(v_a_5049_);
lean_dec(v_a_5048_);
lean_dec_ref(v_a_5047_);
lean_dec(v_a_5046_);
lean_dec_ref(v_a_5045_);
lean_dec(v_a_5044_);
lean_dec_ref(v_a_5043_);
lean_dec(v_a_5042_);
lean_dec(v_a_5041_);
return v_res_5052_;
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
