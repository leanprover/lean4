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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
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
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
v___x_120_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_a_117_, v_a_119_, v_kuv_99_, v_huv_100_, v_kvu_101_, v_a_115_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
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
size_t v_x_278__boxed_259_; size_t v_x_279__boxed_260_; lean_object* v_res_261_; 
v_x_278__boxed_259_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_279__boxed_260_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_261_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_254_, v_k_255_, v_x_256_, v_x_278__boxed_259_, v_x_279__boxed_260_);
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
size_t v_x_148__boxed_453_; size_t v_x_149__boxed_454_; lean_object* v_res_455_; 
v_x_148__boxed_453_ = lean_unbox_usize(v_x_451_);
lean_dec(v_x_451_);
v_x_149__boxed_454_ = lean_unbox_usize(v_x_452_);
lean_dec(v_x_452_);
v_res_455_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_448_, v_p_449_, v_x_450_, v_x_148__boxed_453_, v_x_149__boxed_454_);
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
lean_dec_ref(v___x_649_);
v_sources_651_ = lean_ctor_get(v_a_650_, 18);
lean_inc_ref(v_sources_651_);
lean_dec(v_a_650_);
v_size_652_ = lean_ctor_get(v_sources_651_, 2);
v___x_653_ = lean_box(0);
v___x_654_ = lean_nat_dec_lt(v_u_588_, v_size_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_780__overap_656_; lean_object* v___x_657_; 
lean_dec_ref(v_sources_651_);
v___x_655_ = l_outOfBounds___redArg(v___x_653_);
v___x_780__overap_656_ = l_Lean_AssocList_forM___redArg(v___x_648_, v_f_589_, v___x_655_);
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
v___x_657_ = lean_apply_12(v___x_780__overap_656_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
return v___x_657_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_778__overap_659_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_PersistentArray_get_x21___redArg(v___x_653_, v_sources_651_, v_u_588_);
lean_dec_ref(v_sources_651_);
v___x_778__overap_659_ = l_Lean_AssocList_forM___redArg(v___x_648_, v_f_589_, v___x_658_);
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
v___x_660_ = lean_apply_12(v___x_778__overap_659_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, lean_box(0));
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
lean_dec_ref(v___x_751_);
v_targets_753_ = lean_ctor_get(v_a_752_, 19);
lean_inc_ref(v_targets_753_);
lean_dec(v_a_752_);
v_size_754_ = lean_ctor_get(v_targets_753_, 2);
v___x_755_ = lean_box(0);
v___x_756_ = lean_nat_dec_lt(v_u_690_, v_size_754_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_780__overap_758_; lean_object* v___x_759_; 
lean_dec_ref(v_targets_753_);
v___x_757_ = l_outOfBounds___redArg(v___x_755_);
v___x_780__overap_758_ = l_Lean_AssocList_forM___redArg(v___x_750_, v_f_691_, v___x_757_);
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
v___x_759_ = lean_apply_12(v___x_780__overap_758_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v___x_778__overap_761_; lean_object* v___x_762_; 
v___x_760_ = l_Lean_PersistentArray_get_x21___redArg(v___x_755_, v_targets_753_, v_u_690_);
lean_dec_ref(v_targets_753_);
v___x_778__overap_761_ = l_Lean_AssocList_forM___redArg(v___x_750_, v_f_691_, v___x_760_);
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
v___x_762_ = lean_apply_12(v___x_778__overap_761_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_792_, lean_object* v_v_793_, lean_object* v_k_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_u_792_, v_v_793_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_823_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_823_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_823_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_823_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
if (lean_obj_tag(v_a_808_) == 1)
{
lean_object* v_val_812_; uint8_t v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v_val_812_ = lean_ctor_get(v_a_808_, 0);
lean_inc(v_val_812_);
lean_dec_ref(v_a_808_);
v___x_813_ = l_Lean_Meta_Grind_Order_instDecidableLTWeight(v_k_794_, v_val_812_);
lean_dec(v_val_812_);
v___x_814_ = lean_box(v___x_813_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_814_);
v___x_816_ = v___x_810_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
else
{
uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec(v_a_808_);
v___x_818_ = 1;
v___x_819_ = lean_box(v___x_818_);
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 0, v___x_819_);
v___x_821_ = v___x_810_;
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
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
v_a_824_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_807_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_807_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_832_, lean_object* v_v_833_, lean_object* v_k_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_832_, v_v_833_, v_k_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_k_834_);
lean_dec(v_v_833_);
lean_dec(v_u_832_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_848_, lean_object* v_s_849_){
_start:
{
lean_object* v_id_850_; lean_object* v_type_851_; lean_object* v_u_852_; lean_object* v_isPreorderInst_853_; lean_object* v_leInst_854_; lean_object* v_ltInst_x3f_855_; lean_object* v_isPartialInst_x3f_856_; lean_object* v_isLinearPreInst_x3f_857_; lean_object* v_lawfulOrderLTInst_x3f_858_; lean_object* v_ringId_x3f_859_; uint8_t v_isCommRing_860_; lean_object* v_ringInst_x3f_861_; lean_object* v_orderedRingInst_x3f_862_; lean_object* v_leFn_863_; lean_object* v_ltFn_x3f_864_; lean_object* v_nodes_865_; lean_object* v_nodeMap_866_; lean_object* v_cnstrs_867_; lean_object* v_cnstrsOf_868_; lean_object* v_sources_869_; lean_object* v_targets_870_; lean_object* v_proofs_871_; lean_object* v_propagate_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
v_id_850_ = lean_ctor_get(v_s_849_, 0);
v_type_851_ = lean_ctor_get(v_s_849_, 1);
v_u_852_ = lean_ctor_get(v_s_849_, 2);
v_isPreorderInst_853_ = lean_ctor_get(v_s_849_, 3);
v_leInst_854_ = lean_ctor_get(v_s_849_, 4);
v_ltInst_x3f_855_ = lean_ctor_get(v_s_849_, 5);
v_isPartialInst_x3f_856_ = lean_ctor_get(v_s_849_, 6);
v_isLinearPreInst_x3f_857_ = lean_ctor_get(v_s_849_, 7);
v_lawfulOrderLTInst_x3f_858_ = lean_ctor_get(v_s_849_, 8);
v_ringId_x3f_859_ = lean_ctor_get(v_s_849_, 9);
v_isCommRing_860_ = lean_ctor_get_uint8(v_s_849_, sizeof(void*)*22);
v_ringInst_x3f_861_ = lean_ctor_get(v_s_849_, 10);
v_orderedRingInst_x3f_862_ = lean_ctor_get(v_s_849_, 11);
v_leFn_863_ = lean_ctor_get(v_s_849_, 12);
v_ltFn_x3f_864_ = lean_ctor_get(v_s_849_, 13);
v_nodes_865_ = lean_ctor_get(v_s_849_, 14);
v_nodeMap_866_ = lean_ctor_get(v_s_849_, 15);
v_cnstrs_867_ = lean_ctor_get(v_s_849_, 16);
v_cnstrsOf_868_ = lean_ctor_get(v_s_849_, 17);
v_sources_869_ = lean_ctor_get(v_s_849_, 18);
v_targets_870_ = lean_ctor_get(v_s_849_, 19);
v_proofs_871_ = lean_ctor_get(v_s_849_, 20);
v_propagate_872_ = lean_ctor_get(v_s_849_, 21);
v_isSharedCheck_880_ = !lean_is_exclusive(v_s_849_);
if (v_isSharedCheck_880_ == 0)
{
v___x_874_ = v_s_849_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_propagate_872_);
lean_inc(v_proofs_871_);
lean_inc(v_targets_870_);
lean_inc(v_sources_869_);
lean_inc(v_cnstrsOf_868_);
lean_inc(v_cnstrs_867_);
lean_inc(v_nodeMap_866_);
lean_inc(v_nodes_865_);
lean_inc(v_ltFn_x3f_864_);
lean_inc(v_leFn_863_);
lean_inc(v_orderedRingInst_x3f_862_);
lean_inc(v_ringInst_x3f_861_);
lean_inc(v_ringId_x3f_859_);
lean_inc(v_lawfulOrderLTInst_x3f_858_);
lean_inc(v_isLinearPreInst_x3f_857_);
lean_inc(v_isPartialInst_x3f_856_);
lean_inc(v_ltInst_x3f_855_);
lean_inc(v_leInst_854_);
lean_inc(v_isPreorderInst_853_);
lean_inc(v_u_852_);
lean_inc(v_type_851_);
lean_inc(v_id_850_);
lean_dec(v_s_849_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v_p_848_);
lean_ctor_set(v___x_876_, 1, v_propagate_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 21, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_id_850_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_type_851_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_u_852_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_isPreorderInst_853_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_leInst_854_);
lean_ctor_set(v_reuseFailAlloc_879_, 5, v_ltInst_x3f_855_);
lean_ctor_set(v_reuseFailAlloc_879_, 6, v_isPartialInst_x3f_856_);
lean_ctor_set(v_reuseFailAlloc_879_, 7, v_isLinearPreInst_x3f_857_);
lean_ctor_set(v_reuseFailAlloc_879_, 8, v_lawfulOrderLTInst_x3f_858_);
lean_ctor_set(v_reuseFailAlloc_879_, 9, v_ringId_x3f_859_);
lean_ctor_set(v_reuseFailAlloc_879_, 10, v_ringInst_x3f_861_);
lean_ctor_set(v_reuseFailAlloc_879_, 11, v_orderedRingInst_x3f_862_);
lean_ctor_set(v_reuseFailAlloc_879_, 12, v_leFn_863_);
lean_ctor_set(v_reuseFailAlloc_879_, 13, v_ltFn_x3f_864_);
lean_ctor_set(v_reuseFailAlloc_879_, 14, v_nodes_865_);
lean_ctor_set(v_reuseFailAlloc_879_, 15, v_nodeMap_866_);
lean_ctor_set(v_reuseFailAlloc_879_, 16, v_cnstrs_867_);
lean_ctor_set(v_reuseFailAlloc_879_, 17, v_cnstrsOf_868_);
lean_ctor_set(v_reuseFailAlloc_879_, 18, v_sources_869_);
lean_ctor_set(v_reuseFailAlloc_879_, 19, v_targets_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 20, v_proofs_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 21, v___x_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_879_, sizeof(void*)*22, v_isCommRing_860_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object* v_msgData_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_env_888_; lean_object* v___x_889_; lean_object* v_mctx_890_; lean_object* v_lctx_891_; lean_object* v_options_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_887_ = lean_st_ref_get(v___y_885_);
v_env_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc_ref(v_env_888_);
lean_dec(v___x_887_);
v___x_889_ = lean_st_ref_get(v___y_883_);
v_mctx_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc_ref(v_mctx_890_);
lean_dec(v___x_889_);
v_lctx_891_ = lean_ctor_get(v___y_882_, 2);
v_options_892_ = lean_ctor_get(v___y_884_, 2);
lean_inc_ref(v_options_892_);
lean_inc_ref(v_lctx_891_);
v___x_893_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_893_, 0, v_env_888_);
lean_ctor_set(v___x_893_, 1, v_mctx_890_);
lean_ctor_set(v___x_893_, 2, v_lctx_891_);
lean_ctor_set(v___x_893_, 3, v_options_892_);
v___x_894_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v_msgData_881_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_903_; double v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = lean_float_of_nat(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_908_, lean_object* v_msg_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_ref_915_; lean_object* v___x_916_; lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_961_; 
v_ref_915_ = lean_ctor_get(v___y_912_, 5);
v___x_916_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_961_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_961_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_961_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v_traceState_922_; lean_object* v_env_923_; lean_object* v_nextMacroScope_924_; lean_object* v_ngen_925_; lean_object* v_auxDeclNGen_926_; lean_object* v_cache_927_; lean_object* v_messages_928_; lean_object* v_infoState_929_; lean_object* v_snapshotTasks_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_960_; 
v___x_921_ = lean_st_ref_take(v___y_913_);
v_traceState_922_ = lean_ctor_get(v___x_921_, 4);
v_env_923_ = lean_ctor_get(v___x_921_, 0);
v_nextMacroScope_924_ = lean_ctor_get(v___x_921_, 1);
v_ngen_925_ = lean_ctor_get(v___x_921_, 2);
v_auxDeclNGen_926_ = lean_ctor_get(v___x_921_, 3);
v_cache_927_ = lean_ctor_get(v___x_921_, 5);
v_messages_928_ = lean_ctor_get(v___x_921_, 6);
v_infoState_929_ = lean_ctor_get(v___x_921_, 7);
v_snapshotTasks_930_ = lean_ctor_get(v___x_921_, 8);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_960_ == 0)
{
v___x_932_ = v___x_921_;
v_isShared_933_ = v_isSharedCheck_960_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_snapshotTasks_930_);
lean_inc(v_infoState_929_);
lean_inc(v_messages_928_);
lean_inc(v_cache_927_);
lean_inc(v_traceState_922_);
lean_inc(v_auxDeclNGen_926_);
lean_inc(v_ngen_925_);
lean_inc(v_nextMacroScope_924_);
lean_inc(v_env_923_);
lean_dec(v___x_921_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_960_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
uint64_t v_tid_934_; lean_object* v_traces_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_959_; 
v_tid_934_ = lean_ctor_get_uint64(v_traceState_922_, sizeof(void*)*1);
v_traces_935_ = lean_ctor_get(v_traceState_922_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_traceState_922_);
if (v_isSharedCheck_959_ == 0)
{
v___x_937_ = v_traceState_922_;
v_isShared_938_ = v_isSharedCheck_959_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_traces_935_);
lean_dec(v_traceState_922_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_959_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_939_; double v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_939_ = lean_box(0);
v___x_940_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_941_ = 0;
v___x_942_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_943_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_943_, 0, v_cls_908_);
lean_ctor_set(v___x_943_, 1, v___x_939_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
lean_ctor_set_float(v___x_943_, sizeof(void*)*3, v___x_940_);
lean_ctor_set_float(v___x_943_, sizeof(void*)*3 + 8, v___x_940_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*3 + 16, v___x_941_);
v___x_944_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_945_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v_a_917_);
lean_ctor_set(v___x_945_, 2, v___x_944_);
lean_inc(v_ref_915_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v_ref_915_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_PersistentArray_push___redArg(v_traces_935_, v___x_946_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_947_);
v___x_949_ = v___x_937_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_947_);
lean_ctor_set_uint64(v_reuseFailAlloc_958_, sizeof(void*)*1, v_tid_934_);
v___x_949_ = v_reuseFailAlloc_958_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_951_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 4, v___x_949_);
v___x_951_ = v___x_932_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_env_923_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_nextMacroScope_924_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_ngen_925_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_auxDeclNGen_926_);
lean_ctor_set(v_reuseFailAlloc_957_, 4, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_957_, 5, v_cache_927_);
lean_ctor_set(v_reuseFailAlloc_957_, 6, v_messages_928_);
lean_ctor_set(v_reuseFailAlloc_957_, 7, v_infoState_929_);
lean_ctor_set(v_reuseFailAlloc_957_, 8, v_snapshotTasks_930_);
v___x_951_ = v_reuseFailAlloc_957_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_952_ = lean_st_ref_set(v___y_913_, v___x_951_);
v___x_953_ = lean_box(0);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_953_);
v___x_955_ = v___x_919_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_962_, lean_object* v_msg_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_962_, v_msg_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_cls_982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_984_ = l_Lean_Name_append(v___x_983_, v_cls_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_options_998_; lean_object* v_inheritedTraceOptions_999_; uint8_t v_hasTrace_1000_; lean_object* v___f_1001_; 
v_options_998_ = lean_ctor_get(v_a_995_, 2);
v_inheritedTraceOptions_999_ = lean_ctor_get(v_a_995_, 13);
v_hasTrace_1000_ = lean_ctor_get_uint8(v_options_998_, sizeof(void*)*1);
lean_inc_ref(v_p_985_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_1001_, 0, v_p_985_);
if (v_hasTrace_1000_ == 0)
{
lean_object* v___x_1002_; 
lean_dec_ref(v_p_985_);
v___x_1002_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_986_, v_a_987_);
return v___x_1002_;
}
else
{
lean_object* v_cls_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_cls_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7);
v___x_1005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_999_, v_options_998_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
lean_dec_ref(v_p_985_);
v___x_1006_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_986_, v_a_987_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_Order_ToPropagate_pp(v_p_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1003_, v_a_1008_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; 
lean_dec_ref(v___x_1009_);
v___x_1010_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_986_, v_a_987_);
return v___x_1010_;
}
else
{
lean_dec_ref(v___f_1001_);
return v___x_1009_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___f_1001_);
v_a_1011_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1007_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1007_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1033_, v_msg_1034_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_1048_, lean_object* v_msg_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1048_, v_msg_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1063_, lean_object* v_vals_1064_, lean_object* v_i_1065_, lean_object* v_k_1066_){
_start:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; 
v___x_1067_ = lean_array_get_size(v_keys_1063_);
v___x_1068_ = lean_nat_dec_lt(v_i_1065_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; 
lean_dec(v_i_1065_);
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
else
{
lean_object* v_k_x27_1070_; uint8_t v___x_1071_; 
v_k_x27_1070_ = lean_array_fget_borrowed(v_keys_1063_, v_i_1065_);
v___x_1071_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1066_, v_k_x27_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_i_1065_, v___x_1072_);
lean_dec(v_i_1065_);
v_i_1065_ = v___x_1073_;
goto _start;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_array_fget_borrowed(v_vals_1064_, v_i_1065_);
lean_dec(v_i_1065_);
lean_inc(v___x_1075_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1077_, lean_object* v_vals_1078_, lean_object* v_i_1079_, lean_object* v_k_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1077_, v_vals_1078_, v_i_1079_, v_k_1080_);
lean_dec_ref(v_k_1080_);
lean_dec_ref(v_vals_1078_);
lean_dec_ref(v_keys_1077_);
return v_res_1081_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; 
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_shift_left(v___x_1083_, v___x_1082_);
return v___x_1084_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; 
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0);
v___x_1087_ = lean_usize_sub(v___x_1086_, v___x_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1088_, size_t v_x_1089_, lean_object* v_x_1090_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
lean_object* v_es_1091_; lean_object* v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v_j_1096_; lean_object* v___x_1097_; 
v_es_1091_ = lean_ctor_get(v_x_1088_, 0);
v___x_1092_ = lean_box(2);
v___x_1093_ = ((size_t)5ULL);
v___x_1094_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1);
v___x_1095_ = lean_usize_land(v_x_1089_, v___x_1094_);
v_j_1096_ = lean_usize_to_nat(v___x_1095_);
v___x_1097_ = lean_array_get_borrowed(v___x_1092_, v_es_1091_, v_j_1096_);
lean_dec(v_j_1096_);
switch(lean_obj_tag(v___x_1097_))
{
case 0:
{
lean_object* v_key_1098_; lean_object* v_val_1099_; uint8_t v___x_1100_; 
v_key_1098_ = lean_ctor_get(v___x_1097_, 0);
v_val_1099_ = lean_ctor_get(v___x_1097_, 1);
v___x_1100_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1090_, v_key_1098_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = lean_box(0);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_inc(v_val_1099_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_val_1099_);
return v___x_1102_;
}
}
case 1:
{
lean_object* v_node_1103_; size_t v___x_1104_; 
v_node_1103_ = lean_ctor_get(v___x_1097_, 0);
v___x_1104_ = lean_usize_shift_right(v_x_1089_, v___x_1093_);
v_x_1088_ = v_node_1103_;
v_x_1089_ = v___x_1104_;
goto _start;
}
default: 
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_box(0);
return v___x_1106_;
}
}
}
else
{
lean_object* v_ks_1107_; lean_object* v_vs_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_ks_1107_ = lean_ctor_get(v_x_1088_, 0);
v_vs_1108_ = lean_ctor_get(v_x_1088_, 1);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1107_, v_vs_1108_, v___x_1109_, v_x_1090_);
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
size_t v_x_9944__boxed_1114_; lean_object* v_res_1115_; 
v_x_9944__boxed_1114_ = lean_unbox_usize(v_x_1112_);
lean_dec(v_x_1112_);
v_res_1115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1111_, v_x_9944__boxed_1114_, v_x_1113_);
lean_dec_ref(v_x_1113_);
lean_dec_ref(v_x_1111_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint64_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1117_);
v___x_1119_ = lean_uint64_to_usize(v___x_1118_);
v___x_1120_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1116_, v___x_1119_, v_x_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1121_, v_x_1122_);
lean_dec_ref(v_x_1122_);
lean_dec_ref(v_x_1121_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1133_ = lean_box(0);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1135_ = l_Lean_mkConst(v___x_1134_, v___x_1133_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1136_, lean_object* v_e_1137_, lean_object* v_u_1138_, lean_object* v_v_1139_, lean_object* v_k_1140_, lean_object* v_k_x27_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_h_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___x_1182_; 
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1138_, v_v_1139_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___x_1184_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1138_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1184_);
v___x_1186_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1139_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
v___x_1188_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1185_, v_a_1187_, v_k_1140_, v_a_1183_, v_k_x27_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_h_x3f_1189_; 
v_h_x3f_1189_ = lean_ctor_get(v_c_1136_, 4);
lean_inc(v_h_x3f_1189_);
if (lean_obj_tag(v_h_x3f_1189_) == 1)
{
lean_object* v_a_1190_; lean_object* v_e_1191_; lean_object* v_val_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v_a_1190_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v___x_1188_);
v_e_1191_ = lean_ctor_get(v_c_1136_, 3);
lean_inc_ref(v_e_1191_);
lean_dec_ref(v_c_1136_);
v_val_1192_ = lean_ctor_get(v_h_x3f_1189_, 0);
lean_inc(v_val_1192_);
lean_dec_ref(v_h_x3f_1189_);
v___x_1193_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1137_);
v___x_1194_ = l_Lean_mkApp4(v___x_1193_, v_e_1137_, v_e_1191_, v_val_1192_, v_a_1190_);
v_h_1155_ = v___x_1194_;
v___y_1156_ = v_a_1143_;
v___y_1157_ = v_a_1145_;
v___y_1158_ = v_a_1147_;
v___y_1159_ = v_a_1149_;
v___y_1160_ = v_a_1150_;
v___y_1161_ = v_a_1151_;
v___y_1162_ = v_a_1152_;
goto v___jp_1154_;
}
else
{
lean_object* v_a_1195_; 
lean_dec(v_h_x3f_1189_);
lean_dec_ref(v_c_1136_);
v_a_1195_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v___x_1188_);
v_h_1155_ = v_a_1195_;
v___y_1156_ = v_a_1143_;
v___y_1157_ = v_a_1145_;
v___y_1158_ = v_a_1147_;
v___y_1159_ = v_a_1149_;
v___y_1160_ = v_a_1150_;
v___y_1161_ = v_a_1151_;
v___y_1162_ = v_a_1152_;
goto v___jp_1154_;
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_e_1137_);
lean_dec_ref(v_c_1136_);
v_a_1196_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1188_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1188_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_a_1185_);
lean_dec(v_a_1183_);
lean_dec_ref(v_e_1137_);
lean_dec_ref(v_c_1136_);
v_a_1204_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1186_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1186_);
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
lean_dec(v_a_1183_);
lean_dec_ref(v_e_1137_);
lean_dec_ref(v_c_1136_);
v_a_1212_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1184_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1184_);
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
lean_dec_ref(v_e_1137_);
lean_dec_ref(v_c_1136_);
v_a_1220_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1182_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1182_);
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
v___jp_1154_:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1156_, v___y_1161_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_termMapInv_1165_; lean_object* v___x_1166_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref(v___x_1163_);
v_termMapInv_1165_ = lean_ctor_get(v_a_1164_, 4);
lean_inc_ref(v_termMapInv_1165_);
lean_dec(v_a_1164_);
v___x_1166_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1165_, v_e_1137_);
lean_dec_ref(v_termMapInv_1165_);
if (lean_obj_tag(v___x_1166_) == 1)
{
lean_object* v_val_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v_val_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_val_1167_);
lean_dec_ref(v___x_1166_);
v_fst_1168_ = lean_ctor_get(v_val_1167_, 0);
lean_inc_n(v_fst_1168_, 2);
v_snd_1169_ = lean_ctor_get(v_val_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec(v_val_1167_);
v___x_1170_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1171_ = l_Lean_mkApp4(v___x_1170_, v_fst_1168_, v_e_1137_, v_snd_1169_, v_h_1155_);
v___x_1172_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1168_, v___x_1171_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec(v___x_1166_);
v___x_1173_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1137_, v_h_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
return v___x_1173_;
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_e_1137_);
v_a_1174_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1163_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1163_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1228_ = _args[0];
lean_object* v_e_1229_ = _args[1];
lean_object* v_u_1230_ = _args[2];
lean_object* v_v_1231_ = _args[3];
lean_object* v_k_1232_ = _args[4];
lean_object* v_k_x27_1233_ = _args[5];
lean_object* v_a_1234_ = _args[6];
lean_object* v_a_1235_ = _args[7];
lean_object* v_a_1236_ = _args[8];
lean_object* v_a_1237_ = _args[9];
lean_object* v_a_1238_ = _args[10];
lean_object* v_a_1239_ = _args[11];
lean_object* v_a_1240_ = _args[12];
lean_object* v_a_1241_ = _args[13];
lean_object* v_a_1242_ = _args[14];
lean_object* v_a_1243_ = _args[15];
lean_object* v_a_1244_ = _args[16];
lean_object* v_a_1245_ = _args[17];
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1228_, v_e_1229_, v_u_1230_, v_v_1231_, v_k_1232_, v_k_x27_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_k_x27_1233_);
lean_dec_ref(v_k_1232_);
lean_dec(v_v_1231_);
lean_dec(v_u_1230_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1248_, v_x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1251_, v_x_1252_, v_x_1253_);
lean_dec_ref(v_x_1253_);
lean_dec_ref(v_x_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, size_t v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1256_, v_x_1257_, v_x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_){
_start:
{
size_t v_x_10208__boxed_1264_; lean_object* v_res_1265_; 
v_x_10208__boxed_1264_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_res_1265_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1260_, v_x_1261_, v_x_10208__boxed_1264_, v_x_1263_);
lean_dec_ref(v_x_1263_);
lean_dec_ref(v_x_1261_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1266_, lean_object* v_keys_1267_, lean_object* v_vals_1268_, lean_object* v_heq_1269_, lean_object* v_i_1270_, lean_object* v_k_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1267_, v_vals_1268_, v_i_1270_, v_k_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1273_, lean_object* v_keys_1274_, lean_object* v_vals_1275_, lean_object* v_heq_1276_, lean_object* v_i_1277_, lean_object* v_k_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1273_, v_keys_1274_, v_vals_1275_, v_heq_1276_, v_i_1277_, v_k_1278_);
lean_dec_ref(v_k_1278_);
lean_dec_ref(v_vals_1275_);
lean_dec_ref(v_keys_1274_);
return v_res_1279_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v___x_1294_; lean_object* v___f_1295_; lean_object* v___x_6377__overap_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1295_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1295_, 0, v___x_1294_);
v___x_6377__overap_1296_ = lean_panic_fn_borrowed(v___f_1295_, v_msg_1281_);
lean_dec_ref(v___f_1295_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1290_);
lean_inc_ref(v___y_1289_);
lean_inc(v___y_1288_);
lean_inc_ref(v___y_1287_);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc(v___y_1282_);
v___x_1297_ = lean_apply_12(v___x_6377__overap_1296_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec(v___y_1299_);
return v_res_1311_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1315_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1316_ = lean_unsigned_to_nat(2u);
v___x_1317_ = lean_unsigned_to_nat(86u);
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1319_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1320_ = l_mkPanicMessageWithDecl(v___x_1319_, v___x_1318_, v___x_1317_, v___x_1316_, v___x_1315_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1321_, lean_object* v_e_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_u_1335_; lean_object* v_v_1336_; lean_object* v_e_1337_; lean_object* v_h_x3f_1338_; lean_object* v___x_1339_; 
v_u_1335_ = lean_ctor_get(v_c_1321_, 0);
v_v_1336_ = lean_ctor_get(v_c_1321_, 1);
v_e_1337_ = lean_ctor_get(v_c_1321_, 3);
lean_inc_ref(v_e_1337_);
v_h_x3f_1338_ = lean_ctor_get(v_c_1321_, 4);
lean_inc(v_h_x3f_1338_);
v___x_1339_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1335_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; uint8_t v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_nat_dec_eq(v_u_1335_, v_v_1336_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec(v_a_1340_);
lean_dec(v_h_x3f_1338_);
lean_dec_ref(v_e_1337_);
lean_dec_ref(v_e_1322_);
lean_dec_ref(v_c_1321_);
v___x_1342_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1343_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1342_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1343_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1321_);
lean_dec_ref(v_c_1321_);
v___x_1345_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1340_, v___x_1344_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec_ref(v___x_1344_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_h_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v_h_x3f_1338_) == 1)
{
lean_object* v_val_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v_val_1375_ = lean_ctor_get(v_h_x3f_1338_, 0);
lean_inc(v_val_1375_);
lean_dec_ref(v_h_x3f_1338_);
v___x_1376_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1322_);
v___x_1377_ = l_Lean_mkApp4(v___x_1376_, v_e_1322_, v_e_1337_, v_val_1375_, v_a_1346_);
v_h_1348_ = v___x_1377_;
v___y_1349_ = v_a_1324_;
v___y_1350_ = v_a_1326_;
v___y_1351_ = v_a_1328_;
v___y_1352_ = v_a_1330_;
v___y_1353_ = v_a_1331_;
v___y_1354_ = v_a_1332_;
v___y_1355_ = v_a_1333_;
goto v___jp_1347_;
}
else
{
lean_dec(v_h_x3f_1338_);
lean_dec_ref(v_e_1337_);
v_h_1348_ = v_a_1346_;
v___y_1349_ = v_a_1324_;
v___y_1350_ = v_a_1326_;
v___y_1351_ = v_a_1328_;
v___y_1352_ = v_a_1330_;
v___y_1353_ = v_a_1331_;
v___y_1354_ = v_a_1332_;
v___y_1355_ = v_a_1333_;
goto v___jp_1347_;
}
v___jp_1347_:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1349_, v___y_1354_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v_termMapInv_1358_; lean_object* v___x_1359_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v_termMapInv_1358_ = lean_ctor_get(v_a_1357_, 4);
lean_inc_ref(v_termMapInv_1358_);
lean_dec(v_a_1357_);
v___x_1359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1358_, v_e_1322_);
lean_dec_ref(v_termMapInv_1358_);
if (lean_obj_tag(v___x_1359_) == 1)
{
lean_object* v_val_1360_; lean_object* v_fst_1361_; lean_object* v_snd_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_val_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref(v___x_1359_);
v_fst_1361_ = lean_ctor_get(v_val_1360_, 0);
lean_inc_n(v_fst_1361_, 2);
v_snd_1362_ = lean_ctor_get(v_val_1360_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_val_1360_);
v___x_1363_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1364_ = l_Lean_mkApp4(v___x_1363_, v_fst_1361_, v_e_1322_, v_snd_1362_, v_h_1348_);
v___x_1365_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1361_, v___x_1364_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; 
lean_dec(v___x_1359_);
v___x_1366_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1322_, v_h_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
return v___x_1366_;
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_dec_ref(v_h_1348_);
lean_dec_ref(v_e_1322_);
v_a_1367_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1356_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1356_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v_h_x3f_1338_);
lean_dec_ref(v_e_1337_);
lean_dec_ref(v_e_1322_);
v_a_1378_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1345_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1345_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_h_x3f_1338_);
lean_dec_ref(v_e_1337_);
lean_dec_ref(v_e_1322_);
lean_dec_ref(v_c_1321_);
v_a_1386_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1339_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1339_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1394_, lean_object* v_e_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1394_, v_e_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec_ref(v_a_1399_);
lean_dec(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec(v_a_1396_);
return v_res_1408_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1417_ = l_Lean_mkConst(v___x_1416_, v___x_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1418_, lean_object* v_e_1419_, lean_object* v_u_1420_, lean_object* v_v_1421_, lean_object* v_k_1422_, lean_object* v_k_x27_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_h_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___x_1464_; 
v___x_1464_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1420_, v_v_1421_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1466_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref(v___x_1464_);
v___x_1466_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1420_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1468_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1467_);
lean_dec_ref(v___x_1466_);
v___x_1468_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1421_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1467_, v_a_1469_, v_k_1422_, v_a_1465_, v_k_x27_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_h_x3f_1471_; 
v_h_x3f_1471_ = lean_ctor_get(v_c_1418_, 4);
lean_inc(v_h_x3f_1471_);
if (lean_obj_tag(v_h_x3f_1471_) == 1)
{
lean_object* v_a_1472_; lean_object* v_e_1473_; lean_object* v_val_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v_a_1472_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1470_);
v_e_1473_ = lean_ctor_get(v_c_1418_, 3);
lean_inc_ref(v_e_1473_);
lean_dec_ref(v_c_1418_);
v_val_1474_ = lean_ctor_get(v_h_x3f_1471_, 0);
lean_inc(v_val_1474_);
lean_dec_ref(v_h_x3f_1471_);
v___x_1475_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1419_);
v___x_1476_ = l_Lean_mkApp4(v___x_1475_, v_e_1419_, v_e_1473_, v_val_1474_, v_a_1472_);
v_h_1437_ = v___x_1476_;
v___y_1438_ = v_a_1425_;
v___y_1439_ = v_a_1427_;
v___y_1440_ = v_a_1429_;
v___y_1441_ = v_a_1431_;
v___y_1442_ = v_a_1432_;
v___y_1443_ = v_a_1433_;
v___y_1444_ = v_a_1434_;
goto v___jp_1436_;
}
else
{
lean_object* v_a_1477_; 
lean_dec(v_h_x3f_1471_);
lean_dec_ref(v_c_1418_);
v_a_1477_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1470_);
v_h_1437_ = v_a_1477_;
v___y_1438_ = v_a_1425_;
v___y_1439_ = v_a_1427_;
v___y_1440_ = v_a_1429_;
v___y_1441_ = v_a_1431_;
v___y_1442_ = v_a_1432_;
v___y_1443_ = v_a_1433_;
v___y_1444_ = v_a_1434_;
goto v___jp_1436_;
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec_ref(v_e_1419_);
lean_dec_ref(v_c_1418_);
v_a_1478_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1470_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v_a_1467_);
lean_dec(v_a_1465_);
lean_dec_ref(v_e_1419_);
lean_dec_ref(v_c_1418_);
v_a_1486_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1468_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1468_);
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
lean_dec(v_a_1465_);
lean_dec_ref(v_e_1419_);
lean_dec_ref(v_c_1418_);
v_a_1494_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1466_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1466_);
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
lean_dec_ref(v_e_1419_);
lean_dec_ref(v_c_1418_);
v_a_1502_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1464_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1464_);
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
v___jp_1436_:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1438_, v___y_1443_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v_termMapInv_1447_; lean_object* v___x_1448_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1445_);
v_termMapInv_1447_ = lean_ctor_get(v_a_1446_, 4);
lean_inc_ref(v_termMapInv_1447_);
lean_dec(v_a_1446_);
v___x_1448_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1447_, v_e_1419_);
lean_dec_ref(v_termMapInv_1447_);
if (lean_obj_tag(v___x_1448_) == 1)
{
lean_object* v_val_1449_; lean_object* v_fst_1450_; lean_object* v_snd_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v_val_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_val_1449_);
lean_dec_ref(v___x_1448_);
v_fst_1450_ = lean_ctor_get(v_val_1449_, 0);
lean_inc_n(v_fst_1450_, 2);
v_snd_1451_ = lean_ctor_get(v_val_1449_, 1);
lean_inc(v_snd_1451_);
lean_dec(v_val_1449_);
v___x_1452_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1453_ = l_Lean_mkApp4(v___x_1452_, v_fst_1450_, v_e_1419_, v_snd_1451_, v_h_1437_);
v___x_1454_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1450_, v___x_1453_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v___x_1448_);
v___x_1455_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1419_, v_h_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1455_;
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v_h_1437_);
lean_dec_ref(v_e_1419_);
v_a_1456_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1445_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1445_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1510_ = _args[0];
lean_object* v_e_1511_ = _args[1];
lean_object* v_u_1512_ = _args[2];
lean_object* v_v_1513_ = _args[3];
lean_object* v_k_1514_ = _args[4];
lean_object* v_k_x27_1515_ = _args[5];
lean_object* v_a_1516_ = _args[6];
lean_object* v_a_1517_ = _args[7];
lean_object* v_a_1518_ = _args[8];
lean_object* v_a_1519_ = _args[9];
lean_object* v_a_1520_ = _args[10];
lean_object* v_a_1521_ = _args[11];
lean_object* v_a_1522_ = _args[12];
lean_object* v_a_1523_ = _args[13];
lean_object* v_a_1524_ = _args[14];
lean_object* v_a_1525_ = _args[15];
lean_object* v_a_1526_ = _args[16];
lean_object* v_a_1527_ = _args[17];
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1510_, v_e_1511_, v_u_1512_, v_v_1513_, v_k_1514_, v_k_x27_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_k_x27_1515_);
lean_dec_ref(v_k_1514_);
lean_dec(v_v_1513_);
lean_dec(v_u_1512_);
return v_res_1528_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1531_ = lean_unsigned_to_nat(2u);
v___x_1532_ = lean_unsigned_to_nat(111u);
v___x_1533_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1534_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1535_ = l_mkPanicMessageWithDecl(v___x_1534_, v___x_1533_, v___x_1532_, v___x_1531_, v___x_1530_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1536_, lean_object* v_e_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_){
_start:
{
lean_object* v_u_1550_; lean_object* v_v_1551_; lean_object* v_e_1552_; lean_object* v_h_x3f_1553_; lean_object* v___x_1554_; 
v_u_1550_ = lean_ctor_get(v_c_1536_, 0);
v_v_1551_ = lean_ctor_get(v_c_1536_, 1);
v_e_1552_ = lean_ctor_get(v_c_1536_, 3);
lean_inc_ref(v_e_1552_);
v_h_x3f_1553_ = lean_ctor_get(v_c_1536_, 4);
lean_inc(v_h_x3f_1553_);
v___x_1554_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1550_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; uint8_t v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___x_1556_ = lean_nat_dec_eq(v_u_1550_, v_v_1551_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_dec(v_a_1555_);
lean_dec(v_h_x3f_1553_);
lean_dec_ref(v_e_1552_);
lean_dec_ref(v_e_1537_);
lean_dec_ref(v_c_1536_);
v___x_1557_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1558_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1557_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1536_);
lean_dec_ref(v_c_1536_);
v___x_1560_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1555_, v___x_1559_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec_ref(v___x_1559_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v_h_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v_h_x3f_1553_) == 1)
{
lean_object* v_val_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_val_1590_ = lean_ctor_get(v_h_x3f_1553_, 0);
lean_inc(v_val_1590_);
lean_dec_ref(v_h_x3f_1553_);
v___x_1591_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1537_);
v___x_1592_ = l_Lean_mkApp4(v___x_1591_, v_e_1537_, v_e_1552_, v_val_1590_, v_a_1561_);
v_h_1563_ = v___x_1592_;
v___y_1564_ = v_a_1539_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1543_;
v___y_1567_ = v_a_1545_;
v___y_1568_ = v_a_1546_;
v___y_1569_ = v_a_1547_;
v___y_1570_ = v_a_1548_;
goto v___jp_1562_;
}
else
{
lean_dec(v_h_x3f_1553_);
lean_dec_ref(v_e_1552_);
v_h_1563_ = v_a_1561_;
v___y_1564_ = v_a_1539_;
v___y_1565_ = v_a_1541_;
v___y_1566_ = v_a_1543_;
v___y_1567_ = v_a_1545_;
v___y_1568_ = v_a_1546_;
v___y_1569_ = v_a_1547_;
v___y_1570_ = v_a_1548_;
goto v___jp_1562_;
}
v___jp_1562_:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1564_, v___y_1569_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v_termMapInv_1573_; lean_object* v___x_1574_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v_termMapInv_1573_ = lean_ctor_get(v_a_1572_, 4);
lean_inc_ref(v_termMapInv_1573_);
lean_dec(v_a_1572_);
v___x_1574_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1573_, v_e_1537_);
lean_dec_ref(v_termMapInv_1573_);
if (lean_obj_tag(v___x_1574_) == 1)
{
lean_object* v_val_1575_; lean_object* v_fst_1576_; lean_object* v_snd_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_val_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1575_);
lean_dec_ref(v___x_1574_);
v_fst_1576_ = lean_ctor_get(v_val_1575_, 0);
lean_inc_n(v_fst_1576_, 2);
v_snd_1577_ = lean_ctor_get(v_val_1575_, 1);
lean_inc(v_snd_1577_);
lean_dec(v_val_1575_);
v___x_1578_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1579_ = l_Lean_mkApp4(v___x_1578_, v_fst_1576_, v_e_1537_, v_snd_1577_, v_h_1563_);
v___x_1580_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1576_, v___x_1579_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1580_;
}
else
{
lean_object* v___x_1581_; 
lean_dec(v___x_1574_);
v___x_1581_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1537_, v_h_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1581_;
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_h_1563_);
lean_dec_ref(v_e_1537_);
v_a_1582_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1571_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1571_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_h_x3f_1553_);
lean_dec_ref(v_e_1552_);
lean_dec_ref(v_e_1537_);
v_a_1593_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1560_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1560_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec(v_h_x3f_1553_);
lean_dec_ref(v_e_1552_);
lean_dec_ref(v_e_1537_);
lean_dec_ref(v_c_1536_);
v_a_1601_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1554_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1554_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1609_, lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1609_, v_e_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
lean_dec(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec(v_a_1611_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1625_, v_a_1626_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1638_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_termMapInv_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v_termMapInv_1633_ = lean_ctor_get(v_a_1629_, 4);
lean_inc_ref(v_termMapInv_1633_);
lean_dec(v_a_1629_);
v___x_1634_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1633_, v_e_1624_);
lean_dec_ref(v_termMapInv_1633_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1628_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1628_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1647_, v_a_1648_, v_a_1649_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_e_1647_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1652_, v_a_1653_, v_a_1661_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_e_1665_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1678_){
_start:
{
lean_object* v_id_1679_; lean_object* v_type_1680_; lean_object* v_u_1681_; lean_object* v_isPreorderInst_1682_; lean_object* v_leInst_1683_; lean_object* v_ltInst_x3f_1684_; lean_object* v_isPartialInst_x3f_1685_; lean_object* v_isLinearPreInst_x3f_1686_; lean_object* v_lawfulOrderLTInst_x3f_1687_; lean_object* v_ringId_x3f_1688_; uint8_t v_isCommRing_1689_; lean_object* v_ringInst_x3f_1690_; lean_object* v_orderedRingInst_x3f_1691_; lean_object* v_leFn_1692_; lean_object* v_ltFn_x3f_1693_; lean_object* v_nodes_1694_; lean_object* v_nodeMap_1695_; lean_object* v_cnstrs_1696_; lean_object* v_cnstrsOf_1697_; lean_object* v_sources_1698_; lean_object* v_targets_1699_; lean_object* v_proofs_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_id_1679_ = lean_ctor_get(v_s_1678_, 0);
v_type_1680_ = lean_ctor_get(v_s_1678_, 1);
v_u_1681_ = lean_ctor_get(v_s_1678_, 2);
v_isPreorderInst_1682_ = lean_ctor_get(v_s_1678_, 3);
v_leInst_1683_ = lean_ctor_get(v_s_1678_, 4);
v_ltInst_x3f_1684_ = lean_ctor_get(v_s_1678_, 5);
v_isPartialInst_x3f_1685_ = lean_ctor_get(v_s_1678_, 6);
v_isLinearPreInst_x3f_1686_ = lean_ctor_get(v_s_1678_, 7);
v_lawfulOrderLTInst_x3f_1687_ = lean_ctor_get(v_s_1678_, 8);
v_ringId_x3f_1688_ = lean_ctor_get(v_s_1678_, 9);
v_isCommRing_1689_ = lean_ctor_get_uint8(v_s_1678_, sizeof(void*)*22);
v_ringInst_x3f_1690_ = lean_ctor_get(v_s_1678_, 10);
v_orderedRingInst_x3f_1691_ = lean_ctor_get(v_s_1678_, 11);
v_leFn_1692_ = lean_ctor_get(v_s_1678_, 12);
v_ltFn_x3f_1693_ = lean_ctor_get(v_s_1678_, 13);
v_nodes_1694_ = lean_ctor_get(v_s_1678_, 14);
v_nodeMap_1695_ = lean_ctor_get(v_s_1678_, 15);
v_cnstrs_1696_ = lean_ctor_get(v_s_1678_, 16);
v_cnstrsOf_1697_ = lean_ctor_get(v_s_1678_, 17);
v_sources_1698_ = lean_ctor_get(v_s_1678_, 18);
v_targets_1699_ = lean_ctor_get(v_s_1678_, 19);
v_proofs_1700_ = lean_ctor_get(v_s_1678_, 20);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_s_1678_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_s_1678_, 21);
lean_dec(v_unused_1709_);
v___x_1702_ = v_s_1678_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_proofs_1700_);
lean_inc(v_targets_1699_);
lean_inc(v_sources_1698_);
lean_inc(v_cnstrsOf_1697_);
lean_inc(v_cnstrs_1696_);
lean_inc(v_nodeMap_1695_);
lean_inc(v_nodes_1694_);
lean_inc(v_ltFn_x3f_1693_);
lean_inc(v_leFn_1692_);
lean_inc(v_orderedRingInst_x3f_1691_);
lean_inc(v_ringInst_x3f_1690_);
lean_inc(v_ringId_x3f_1688_);
lean_inc(v_lawfulOrderLTInst_x3f_1687_);
lean_inc(v_isLinearPreInst_x3f_1686_);
lean_inc(v_isPartialInst_x3f_1685_);
lean_inc(v_ltInst_x3f_1684_);
lean_inc(v_leInst_1683_);
lean_inc(v_isPreorderInst_1682_);
lean_inc(v_u_1681_);
lean_inc(v_type_1680_);
lean_inc(v_id_1679_);
lean_dec(v_s_1678_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_box(0);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 21, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_id_1679_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_type_1680_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_u_1681_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_isPreorderInst_1682_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_leInst_1683_);
lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_ltInst_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_isPartialInst_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1707_, 7, v_isLinearPreInst_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1707_, 8, v_lawfulOrderLTInst_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1707_, 9, v_ringId_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1707_, 10, v_ringInst_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1707_, 11, v_orderedRingInst_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1707_, 12, v_leFn_1692_);
lean_ctor_set(v_reuseFailAlloc_1707_, 13, v_ltFn_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1707_, 14, v_nodes_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 15, v_nodeMap_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 16, v_cnstrs_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 17, v_cnstrsOf_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 18, v_sources_1698_);
lean_ctor_set(v_reuseFailAlloc_1707_, 19, v_targets_1699_);
lean_ctor_set(v_reuseFailAlloc_1707_, 20, v_proofs_1700_);
lean_ctor_set(v_reuseFailAlloc_1707_, 21, v___x_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1707_, sizeof(void*)*22, v_isCommRing_1689_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1718_ = l_Lean_mkConst(v___x_1717_, v___x_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
if (lean_obj_tag(v_as_x27_1719_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_b_1720_);
return v___x_1733_;
}
else
{
lean_object* v_head_1734_; lean_object* v_tail_1735_; lean_object* v___x_1736_; 
v_head_1734_ = lean_ctor_get(v_as_x27_1719_, 0);
v_tail_1735_ = lean_ctor_get(v_as_x27_1719_, 1);
v___x_1736_ = lean_box(0);
switch(lean_obj_tag(v_head_1734_))
{
case 0:
{
lean_object* v_c_1737_; lean_object* v_e_1738_; lean_object* v_u_1739_; lean_object* v_v_1740_; lean_object* v_k_1741_; lean_object* v_k_x27_1742_; lean_object* v___x_1743_; 
v_c_1737_ = lean_ctor_get(v_head_1734_, 0);
v_e_1738_ = lean_ctor_get(v_head_1734_, 1);
v_u_1739_ = lean_ctor_get(v_head_1734_, 2);
v_v_1740_ = lean_ctor_get(v_head_1734_, 3);
v_k_1741_ = lean_ctor_get(v_head_1734_, 4);
v_k_x27_1742_ = lean_ctor_get(v_head_1734_, 5);
lean_inc_ref(v_e_1738_);
lean_inc_ref(v_c_1737_);
v___x_1743_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1737_, v_e_1738_, v_u_1739_, v_v_1740_, v_k_1741_, v_k_x27_1742_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_dec_ref(v___x_1743_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
return v___x_1743_;
}
}
case 1:
{
lean_object* v_c_1745_; lean_object* v_e_1746_; lean_object* v_u_1747_; lean_object* v_v_1748_; lean_object* v_k_1749_; lean_object* v_k_x27_1750_; lean_object* v___x_1751_; 
v_c_1745_ = lean_ctor_get(v_head_1734_, 0);
v_e_1746_ = lean_ctor_get(v_head_1734_, 1);
v_u_1747_ = lean_ctor_get(v_head_1734_, 2);
v_v_1748_ = lean_ctor_get(v_head_1734_, 3);
v_k_1749_ = lean_ctor_get(v_head_1734_, 4);
v_k_x27_1750_ = lean_ctor_get(v_head_1734_, 5);
lean_inc_ref(v_e_1746_);
lean_inc_ref(v_c_1745_);
v___x_1751_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1745_, v_e_1746_, v_u_1747_, v_v_1748_, v_k_1749_, v_k_x27_1750_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref(v___x_1751_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
return v___x_1751_;
}
}
default: 
{
lean_object* v_u_1753_; lean_object* v_v_1754_; lean_object* v___x_1755_; 
v_u_1753_ = lean_ctor_get(v_head_1734_, 0);
v_v_1754_ = lean_ctor_get(v_head_1734_, 1);
v___x_1755_ = l_Lean_Meta_Grind_Order_getExpr(v_u_1753_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___x_1757_ = l_Lean_Meta_Grind_Order_getExpr(v_v_1754_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1879_; lean_object* v___x_1933_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1933_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1756_, v___y_1722_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
v___x_1935_ = lean_unbox(v_a_1934_);
lean_dec(v_a_1934_);
if (v___x_1935_ == 0)
{
v___y_1879_ = v___x_1933_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1936_; 
lean_dec_ref(v___x_1933_);
v___x_1936_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1758_, v___y_1722_);
v___y_1879_ = v___x_1936_;
goto v___jp_1878_;
}
}
else
{
v___y_1879_ = v___x_1933_;
goto v___jp_1878_;
}
v___jp_1759_:
{
if (lean_obj_tag(v___y_1775_) == 0)
{
lean_object* v_a_1776_; uint8_t v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___y_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___y_1775_);
v___x_1777_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1771_, v___y_1767_, v___y_1766_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; uint8_t v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v___x_1781_ = lean_unbox(v_a_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1753_, v_v_1754_, v___y_1765_, v___y_1766_, v___y_1770_, v___y_1761_, v___y_1760_, v___y_1768_, v___y_1769_, v___y_1762_, v___y_1763_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1765_, v___y_1766_, v___y_1770_, v___y_1761_, v___y_1760_, v___y_1768_, v___y_1769_, v___y_1762_, v___y_1763_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1786_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1783_, v_a_1785_, v___y_1765_, v___y_1766_, v___y_1770_, v___y_1761_, v___y_1760_, v___y_1768_, v___y_1769_, v___y_1762_, v___y_1763_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; lean_object* v___x_1791_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
v___x_1788_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1767_);
lean_inc_ref(v___y_1771_);
v___x_1789_ = l_Lean_mkApp7(v___x_1788_, v___y_1771_, v___y_1767_, v_a_1756_, v_a_1758_, v___y_1772_, v___y_1764_, v_a_1787_);
v___x_1790_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
v___x_1791_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1771_, v___y_1767_, v___x_1789_, v___x_1790_, v___y_1766_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1774_, v___y_1773_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref(v___x_1791_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
return v___x_1791_;
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1793_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1786_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1786_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec(v_a_1783_);
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1801_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1784_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1784_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1809_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1782_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1782_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1818_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1779_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1779_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1767_);
lean_dec_ref(v___y_1764_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1826_ = lean_ctor_get(v___y_1775_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___y_1775_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___y_1775_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
v___jp_1834_:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1756_, v___y_1836_, v___y_1844_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
if (lean_obj_tag(v_a_1847_) == 1)
{
lean_object* v_val_1848_; lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1851_; 
v_val_1848_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_val_1848_);
lean_dec_ref(v_a_1847_);
v_fst_1849_ = lean_ctor_get(v_val_1848_, 0);
lean_inc(v_fst_1849_);
v_snd_1850_ = lean_ctor_get(v_val_1848_, 1);
lean_inc(v_snd_1850_);
lean_dec(v_val_1848_);
v___x_1851_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1758_, v___y_1836_, v___y_1844_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
if (lean_obj_tag(v_a_1852_) == 1)
{
lean_object* v_val_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1856_; 
v_val_1853_ = lean_ctor_get(v_a_1852_, 0);
lean_inc(v_val_1853_);
lean_dec_ref(v_a_1852_);
v_fst_1854_ = lean_ctor_get(v_val_1853_, 0);
lean_inc(v_fst_1854_);
v_snd_1855_ = lean_ctor_get(v_val_1853_, 1);
lean_inc(v_snd_1855_);
lean_dec(v_val_1853_);
v___x_1856_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1849_, v___y_1836_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; uint8_t v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
v___x_1858_ = lean_unbox(v_a_1857_);
lean_dec(v_a_1857_);
if (v___x_1858_ == 0)
{
v___y_1760_ = v___y_1839_;
v___y_1761_ = v___y_1838_;
v___y_1762_ = v___y_1842_;
v___y_1763_ = v___y_1843_;
v___y_1764_ = v_snd_1855_;
v___y_1765_ = v___y_1835_;
v___y_1766_ = v___y_1836_;
v___y_1767_ = v_fst_1854_;
v___y_1768_ = v___y_1840_;
v___y_1769_ = v___y_1841_;
v___y_1770_ = v___y_1837_;
v___y_1771_ = v_fst_1849_;
v___y_1772_ = v_snd_1850_;
v___y_1773_ = v___y_1845_;
v___y_1774_ = v___y_1844_;
v___y_1775_ = v___x_1856_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1859_; 
lean_dec_ref(v___x_1856_);
v___x_1859_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1854_, v___y_1836_);
v___y_1760_ = v___y_1839_;
v___y_1761_ = v___y_1838_;
v___y_1762_ = v___y_1842_;
v___y_1763_ = v___y_1843_;
v___y_1764_ = v_snd_1855_;
v___y_1765_ = v___y_1835_;
v___y_1766_ = v___y_1836_;
v___y_1767_ = v_fst_1854_;
v___y_1768_ = v___y_1840_;
v___y_1769_ = v___y_1841_;
v___y_1770_ = v___y_1837_;
v___y_1771_ = v_fst_1849_;
v___y_1772_ = v_snd_1850_;
v___y_1773_ = v___y_1845_;
v___y_1774_ = v___y_1844_;
v___y_1775_ = v___x_1859_;
goto v___jp_1759_;
}
}
else
{
v___y_1760_ = v___y_1839_;
v___y_1761_ = v___y_1838_;
v___y_1762_ = v___y_1842_;
v___y_1763_ = v___y_1843_;
v___y_1764_ = v_snd_1855_;
v___y_1765_ = v___y_1835_;
v___y_1766_ = v___y_1836_;
v___y_1767_ = v_fst_1854_;
v___y_1768_ = v___y_1840_;
v___y_1769_ = v___y_1841_;
v___y_1770_ = v___y_1837_;
v___y_1771_ = v_fst_1849_;
v___y_1772_ = v_snd_1850_;
v___y_1773_ = v___y_1845_;
v___y_1774_ = v___y_1844_;
v___y_1775_ = v___x_1856_;
goto v___jp_1759_;
}
}
else
{
lean_dec(v_a_1852_);
lean_dec(v_snd_1850_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_snd_1850_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1861_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1851_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1851_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_dec(v_a_1847_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1870_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1846_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1846_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
v___jp_1878_:
{
if (lean_obj_tag(v___y_1879_) == 0)
{
lean_object* v_a_1880_; uint8_t v___x_1881_; 
v_a_1880_ = lean_ctor_get(v___y_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___y_1879_);
v___x_1881_ = lean_unbox(v_a_1880_);
lean_dec(v_a_1880_);
if (v___x_1881_ == 0)
{
v___y_1835_ = v___y_1721_;
v___y_1836_ = v___y_1722_;
v___y_1837_ = v___y_1723_;
v___y_1838_ = v___y_1724_;
v___y_1839_ = v___y_1725_;
v___y_1840_ = v___y_1726_;
v___y_1841_ = v___y_1727_;
v___y_1842_ = v___y_1728_;
v___y_1843_ = v___y_1729_;
v___y_1844_ = v___y_1730_;
v___y_1845_ = v___y_1731_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1756_, v_a_1758_, v___y_1722_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; uint8_t v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = lean_unbox(v_a_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1753_, v_v_1754_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1889_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1886_, v_a_1888_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; uint8_t v___x_1891_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
v___x_1891_ = lean_unbox(v_a_1883_);
lean_dec(v_a_1883_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1892_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1756_, v_a_1758_, v_a_1890_, v___x_1891_, v___y_1722_, v___y_1724_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_dec_ref(v___x_1892_);
v___y_1835_ = v___y_1721_;
v___y_1836_ = v___y_1722_;
v___y_1837_ = v___y_1723_;
v___y_1838_ = v___y_1724_;
v___y_1839_ = v___y_1725_;
v___y_1840_ = v___y_1726_;
v___y_1841_ = v___y_1727_;
v___y_1842_ = v___y_1728_;
v___y_1843_ = v___y_1729_;
v___y_1844_ = v___y_1730_;
v___y_1845_ = v___y_1731_;
goto v___jp_1834_;
}
else
{
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
return v___x_1892_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1883_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1893_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1889_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1889_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v_a_1886_);
lean_dec(v_a_1883_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1901_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1887_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1887_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1883_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1909_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1885_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1885_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_dec(v_a_1883_);
v___y_1835_ = v___y_1721_;
v___y_1836_ = v___y_1722_;
v___y_1837_ = v___y_1723_;
v___y_1838_ = v___y_1724_;
v___y_1839_ = v___y_1725_;
v___y_1840_ = v___y_1726_;
v___y_1841_ = v___y_1727_;
v___y_1842_ = v___y_1728_;
v___y_1843_ = v___y_1729_;
v___y_1844_ = v___y_1730_;
v___y_1845_ = v___y_1731_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1917_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1882_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1882_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1925_ = lean_ctor_get(v___y_1879_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___y_1879_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___y_1879_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___y_1879_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
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
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_dec(v_a_1756_);
v_a_1937_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1757_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1757_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1755_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1755_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1953_, lean_object* v_b_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1953_, v_b_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
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
lean_dec(v_as_x27_1953_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_Meta_Grind_Order_getStruct(v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___f_1983_; lean_object* v___x_1984_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1981_);
v___f_1983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_1984_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1983_, v_a_1969_, v_a_1970_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_propagate_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec_ref(v___x_1984_);
v_propagate_1985_ = lean_ctor_get(v_a_1982_, 21);
lean_inc(v_propagate_1985_);
lean_dec(v_a_1982_);
v___x_1986_ = lean_box(0);
v___x_1987_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_1985_, v___x_1986_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_propagate_1985_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1987_, 0);
lean_dec(v_unused_1995_);
v___x_1989_ = v___x_1987_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_dec(v___x_1987_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_1986_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1986_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
else
{
return v___x_1987_;
}
}
else
{
lean_dec(v_a_1982_);
return v___x_1984_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v_a_1996_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1981_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1981_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec(v_a_2004_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2017_, lean_object* v_as_x27_2018_, lean_object* v_b_2019_, lean_object* v_a_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2018_, v_b_2019_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2034_, lean_object* v_as_x27_2035_, lean_object* v_b_2036_, lean_object* v_a_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2034_, v_as_x27_2035_, v_b_2036_, v_a_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v_as_x27_2035_);
lean_dec(v_as_2034_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2052_, v_a_2056_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v_termMapInv_2061_; lean_object* v___x_2062_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2059_);
v_termMapInv_2061_ = lean_ctor_get(v_a_2060_, 4);
lean_inc_ref(v_termMapInv_2061_);
lean_dec(v_a_2060_);
v___x_2062_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2061_, v_e_2051_);
lean_dec_ref(v_termMapInv_2061_);
if (lean_obj_tag(v___x_2062_) == 1)
{
lean_object* v_val_2063_; lean_object* v_fst_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v_e_2051_);
v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_val_2063_);
lean_dec_ref(v___x_2062_);
v_fst_2064_ = lean_ctor_get(v_val_2063_, 0);
lean_inc(v_fst_2064_);
lean_dec(v_val_2063_);
v___x_2065_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2064_, v_a_2052_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; uint8_t v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
v___x_2067_ = lean_unbox(v_a_2066_);
lean_dec(v_a_2066_);
if (v___x_2067_ == 0)
{
lean_dec(v_fst_2064_);
return v___x_2065_;
}
else
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_2065_);
v___x_2068_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2064_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
return v___x_2068_;
}
}
else
{
lean_dec(v_fst_2064_);
return v___x_2065_;
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v___x_2062_);
v___x_2069_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2051_, v_a_2052_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
v___x_2071_ = lean_unbox(v_a_2070_);
lean_dec(v_a_2070_);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_e_2051_);
return v___x_2069_;
}
else
{
lean_object* v___x_2072_; 
lean_dec_ref(v___x_2069_);
v___x_2072_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
return v___x_2072_;
}
}
else
{
lean_dec_ref(v_e_2051_);
return v___x_2069_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_e_2051_);
v_a_2073_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2059_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2059_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2087_);
lean_dec_ref(v_a_2086_);
lean_dec(v_a_2085_);
lean_dec_ref(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec(v_a_2082_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2090_, v_a_2092_, v_a_2096_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec_ref(v_a_2112_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec(v_a_2105_);
return v_res_2117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2126_ = l_Lean_Name_append(v___x_2125_, v___x_2124_);
return v___x_2126_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2131_, lean_object* v_v_2132_, lean_object* v_k_2133_, lean_object* v_c_2134_, lean_object* v_e_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v___x_2148_; 
lean_inc_ref(v_e_2135_);
v___x_2148_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2135_, v_a_2137_, v_a_2141_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2247_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2151_ = v___x_2148_;
v_isShared_2152_ = v_isSharedCheck_2247_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2148_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2247_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
uint8_t v___x_2153_; 
v___x_2153_ = lean_unbox(v_a_2149_);
lean_dec(v_a_2149_);
if (v___x_2153_ == 0)
{
lean_object* v_options_2154_; lean_object* v_inheritedTraceOptions_2155_; uint8_t v_hasTrace_2156_; lean_object* v___x_2157_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; 
v_options_2154_ = lean_ctor_get(v_a_2145_, 2);
v_inheritedTraceOptions_2155_ = lean_ctor_get(v_a_2145_, 13);
v_hasTrace_2156_ = lean_ctor_get_uint8(v_options_2154_, sizeof(void*)*1);
v___x_2157_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2134_);
if (v_hasTrace_2156_ == 0)
{
v___y_2159_ = v_a_2136_;
v___y_2160_ = v_a_2137_;
v___y_2161_ = v_a_2138_;
v___y_2162_ = v_a_2139_;
v___y_2163_ = v_a_2140_;
v___y_2164_ = v_a_2141_;
v___y_2165_ = v_a_2142_;
v___y_2166_ = v_a_2143_;
v___y_2167_ = v_a_2144_;
v___y_2168_ = v_a_2145_;
v___y_2169_ = v_a_2146_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2155_, v_options_2154_, v___x_2178_);
if (v___x_2179_ == 0)
{
v___y_2159_ = v_a_2136_;
v___y_2160_ = v_a_2137_;
v___y_2161_ = v_a_2138_;
v___y_2162_ = v_a_2139_;
v___y_2163_ = v_a_2140_;
v___y_2164_ = v_a_2141_;
v___y_2165_ = v_a_2142_;
v___y_2166_ = v_a_2143_;
v___y_2167_ = v_a_2144_;
v___y_2168_ = v_a_2145_;
v___y_2169_ = v_a_2146_;
goto v___jp_2158_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2131_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
v___x_2182_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2132_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; lean_object* v___x_2184_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2134_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_k_2186_; uint8_t v_strict_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___y_2204_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
v_k_2186_ = lean_ctor_get(v_k_2133_, 0);
v_strict_2187_ = lean_ctor_get_uint8(v_k_2133_, sizeof(void*)*1);
v___x_2188_ = l_Lean_MessageData_ofExpr(v_a_2181_);
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2188_);
lean_ctor_set(v___x_2199_, 1, v___x_2189_);
v___x_2200_ = l_Lean_MessageData_ofExpr(v_a_2183_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2189_);
if (v_strict_2187_ == 0)
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Int_repr(v_k_2186_);
v___y_2204_ = v___x_2215_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2216_ = l_Int_repr(v_k_2186_);
v___x_2217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2218_ = lean_string_append(v___x_2216_, v___x_2217_);
v___y_2204_ = v___x_2218_;
goto v___jp_2203_;
}
v___jp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2192_);
v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___y_2191_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2189_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v_a_2185_);
v___x_2198_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2177_, v___x_2197_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_dec_ref(v___x_2198_);
v___y_2159_ = v_a_2136_;
v___y_2160_ = v_a_2137_;
v___y_2161_ = v_a_2138_;
v___y_2162_ = v_a_2139_;
v___y_2163_ = v_a_2140_;
v___y_2164_ = v_a_2141_;
v___y_2165_ = v_a_2142_;
v___y_2166_ = v_a_2143_;
v___y_2167_ = v_a_2144_;
v___y_2168_ = v_a_2145_;
v___y_2169_ = v_a_2146_;
goto v___jp_2158_;
}
else
{
lean_dec_ref(v___x_2157_);
lean_del_object(v___x_2151_);
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
return v___x_2198_;
}
}
v___jp_2203_:
{
lean_object* v_k_2205_; uint8_t v_strict_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v_k_2205_ = lean_ctor_get(v___x_2157_, 0);
lean_inc(v_k_2205_);
v_strict_2206_ = lean_ctor_get_uint8(v___x_2157_, sizeof(void*)*1);
v___x_2207_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___y_2204_);
v___x_2208_ = l_Lean_MessageData_ofFormat(v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2202_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2189_);
if (v_strict_2206_ == 0)
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Int_repr(v_k_2205_);
lean_dec(v_k_2205_);
v___y_2191_ = v___x_2210_;
v___y_2192_ = v___x_2211_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = l_Int_repr(v_k_2205_);
lean_dec(v_k_2205_);
v___x_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2214_ = lean_string_append(v___x_2212_, v___x_2213_);
v___y_2191_ = v___x_2210_;
v___y_2192_ = v___x_2214_;
goto v___jp_2190_;
}
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec(v_a_2183_);
lean_dec(v_a_2181_);
lean_dec_ref(v___x_2157_);
lean_del_object(v___x_2151_);
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v_a_2219_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2184_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2184_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2181_);
lean_dec_ref(v___x_2157_);
lean_del_object(v___x_2151_);
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v_a_2227_ = lean_ctor_get(v___x_2182_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2182_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2182_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2182_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec_ref(v___x_2157_);
lean_del_object(v___x_2151_);
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v_a_2235_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2180_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2180_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
v___jp_2158_:
{
uint8_t v___x_2170_; 
v___x_2170_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2133_, v___x_2157_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
lean_dec_ref(v___x_2157_);
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v___x_2171_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2171_);
v___x_2173_ = v___x_2151_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_del_object(v___x_2151_);
v___x_2175_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2175_, 0, v_c_2134_);
lean_ctor_set(v___x_2175_, 1, v_e_2135_);
lean_ctor_set(v___x_2175_, 2, v_u_2131_);
lean_ctor_set(v___x_2175_, 3, v_v_2132_);
lean_ctor_set(v___x_2175_, 4, v_k_2133_);
lean_ctor_set(v___x_2175_, 5, v___x_2157_);
v___x_2176_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2175_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
return v___x_2176_;
}
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v___x_2243_ = lean_box(0);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2243_);
v___x_2245_ = v___x_2151_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_e_2135_);
lean_dec_ref(v_c_2134_);
lean_dec_ref(v_k_2133_);
lean_dec(v_v_2132_);
lean_dec(v_u_2131_);
v_a_2248_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2148_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2148_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2256_ = _args[0];
lean_object* v_v_2257_ = _args[1];
lean_object* v_k_2258_ = _args[2];
lean_object* v_c_2259_ = _args[3];
lean_object* v_e_2260_ = _args[4];
lean_object* v_a_2261_ = _args[5];
lean_object* v_a_2262_ = _args[6];
lean_object* v_a_2263_ = _args[7];
lean_object* v_a_2264_ = _args[8];
lean_object* v_a_2265_ = _args[9];
lean_object* v_a_2266_ = _args[10];
lean_object* v_a_2267_ = _args[11];
lean_object* v_a_2268_ = _args[12];
lean_object* v_a_2269_ = _args[13];
lean_object* v_a_2270_ = _args[14];
lean_object* v_a_2271_ = _args[15];
lean_object* v_a_2272_ = _args[16];
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2256_, v_v_2257_, v_k_2258_, v_c_2259_, v_e_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec(v_a_2262_);
lean_dec(v_a_2261_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2275_, v_a_2279_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v_termMapInv_2284_; lean_object* v___x_2285_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
v_termMapInv_2284_ = lean_ctor_get(v_a_2283_, 4);
lean_inc_ref(v_termMapInv_2284_);
lean_dec(v_a_2283_);
v___x_2285_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2284_, v_e_2274_);
lean_dec_ref(v_termMapInv_2284_);
if (lean_obj_tag(v___x_2285_) == 1)
{
lean_object* v_val_2286_; lean_object* v_fst_2287_; lean_object* v___x_2288_; 
lean_dec_ref(v_e_2274_);
v_val_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_val_2286_);
lean_dec_ref(v___x_2285_);
v_fst_2287_ = lean_ctor_get(v_val_2286_, 0);
lean_inc(v_fst_2287_);
lean_dec(v_val_2286_);
v___x_2288_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2287_, v_a_2275_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; uint8_t v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
v___x_2290_ = lean_unbox(v_a_2289_);
lean_dec(v_a_2289_);
if (v___x_2290_ == 0)
{
lean_dec(v_fst_2287_);
return v___x_2288_;
}
else
{
lean_object* v___x_2291_; 
lean_dec_ref(v___x_2288_);
v___x_2291_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2287_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2291_;
}
}
else
{
lean_dec(v_fst_2287_);
return v___x_2288_;
}
}
else
{
lean_object* v___x_2292_; 
lean_dec(v___x_2285_);
v___x_2292_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2274_, v_a_2275_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v_a_2293_; uint8_t v___x_2294_; 
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_a_2293_);
v___x_2294_ = lean_unbox(v_a_2293_);
lean_dec(v_a_2293_);
if (v___x_2294_ == 0)
{
lean_dec_ref(v_e_2274_);
return v___x_2292_;
}
else
{
lean_object* v___x_2295_; 
lean_dec_ref(v___x_2292_);
v___x_2295_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
return v___x_2295_;
}
}
else
{
lean_dec_ref(v_e_2274_);
return v___x_2292_;
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_e_2274_);
v_a_2296_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2282_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2282_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2313_, v_a_2315_, v_a_2319_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
lean_dec(v_a_2338_);
lean_dec_ref(v_a_2337_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec(v_a_2328_);
return v_res_2340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2349_ = l_Lean_Name_append(v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2352_ = l_Lean_stringToMessageData(v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2353_, lean_object* v_v_2354_, lean_object* v_k_2355_, lean_object* v_c_2356_, lean_object* v_e_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___x_2370_; 
lean_inc_ref(v_e_2357_);
v___x_2370_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2357_, v_a_2359_, v_a_2363_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2370_) == 0)
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2471_; 
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2471_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2471_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_unbox(v_a_2371_);
lean_dec(v_a_2371_);
if (v___x_2375_ == 0)
{
lean_object* v_options_2376_; lean_object* v_inheritedTraceOptions_2377_; uint8_t v_hasTrace_2378_; lean_object* v___x_2379_; lean_object* v___y_2381_; lean_object* v___y_2382_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; 
v_options_2376_ = lean_ctor_get(v_a_2367_, 2);
v_inheritedTraceOptions_2377_ = lean_ctor_get(v_a_2367_, 13);
v_hasTrace_2378_ = lean_ctor_get_uint8(v_options_2376_, sizeof(void*)*1);
v___x_2379_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2356_);
if (v_hasTrace_2378_ == 0)
{
v___y_2381_ = v_a_2358_;
v___y_2382_ = v_a_2359_;
v___y_2383_ = v_a_2360_;
v___y_2384_ = v_a_2361_;
v___y_2385_ = v_a_2362_;
v___y_2386_ = v_a_2363_;
v___y_2387_ = v_a_2364_;
v___y_2388_ = v_a_2365_;
v___y_2389_ = v_a_2366_;
v___y_2390_ = v_a_2367_;
v___y_2391_ = v_a_2368_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; uint8_t v___x_2402_; 
v___x_2400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2402_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2377_, v_options_2376_, v___x_2401_);
if (v___x_2402_ == 0)
{
v___y_2381_ = v_a_2358_;
v___y_2382_ = v_a_2359_;
v___y_2383_ = v_a_2360_;
v___y_2384_ = v_a_2361_;
v___y_2385_ = v_a_2362_;
v___y_2386_ = v_a_2363_;
v___y_2387_ = v_a_2364_;
v___y_2388_ = v_a_2365_;
v___y_2389_ = v_a_2366_;
v___y_2390_ = v_a_2367_;
v___y_2391_ = v_a_2368_;
goto v___jp_2380_;
}
else
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2353_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref(v___x_2403_);
v___x_2405_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2354_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref(v___x_2405_);
v___x_2407_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2356_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v_k_2419_; uint8_t v_strict_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___y_2428_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref(v___x_2407_);
v_k_2419_ = lean_ctor_get(v_k_2355_, 0);
v_strict_2420_ = lean_ctor_get_uint8(v_k_2355_, sizeof(void*)*1);
v___x_2421_ = l_Lean_MessageData_ofExpr(v_a_2404_);
v___x_2422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_MessageData_ofExpr(v_a_2406_);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
lean_ctor_set(v___x_2426_, 1, v___x_2422_);
if (v_strict_2420_ == 0)
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Int_repr(v_k_2419_);
v___y_2428_ = v___x_2439_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = l_Int_repr(v_k_2419_);
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2442_ = lean_string_append(v___x_2440_, v___x_2441_);
v___y_2428_ = v___x_2442_;
goto v___jp_2427_;
}
v___jp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___y_2411_);
v___x_2413_ = l_Lean_MessageData_ofFormat(v___x_2412_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___y_2410_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2414_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2416_);
lean_ctor_set(v___x_2417_, 1, v_a_2408_);
v___x_2418_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2400_, v___x_2417_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_dec_ref(v___x_2418_);
v___y_2381_ = v_a_2358_;
v___y_2382_ = v_a_2359_;
v___y_2383_ = v_a_2360_;
v___y_2384_ = v_a_2361_;
v___y_2385_ = v_a_2362_;
v___y_2386_ = v_a_2363_;
v___y_2387_ = v_a_2364_;
v___y_2388_ = v_a_2365_;
v___y_2389_ = v_a_2366_;
v___y_2390_ = v_a_2367_;
v___y_2391_ = v_a_2368_;
goto v___jp_2380_;
}
else
{
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
return v___x_2418_;
}
}
v___jp_2427_:
{
lean_object* v_k_2429_; uint8_t v_strict_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v_k_2429_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_k_2429_);
v_strict_2430_ = lean_ctor_get_uint8(v___x_2379_, sizeof(void*)*1);
v___x_2431_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___y_2428_);
v___x_2432_ = l_Lean_MessageData_ofFormat(v___x_2431_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2426_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2422_);
if (v_strict_2430_ == 0)
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Int_repr(v_k_2429_);
lean_dec(v_k_2429_);
v___y_2410_ = v___x_2434_;
v___y_2411_ = v___x_2435_;
goto v___jp_2409_;
}
else
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = l_Int_repr(v_k_2429_);
lean_dec(v_k_2429_);
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2438_ = lean_string_append(v___x_2436_, v___x_2437_);
v___y_2410_ = v___x_2434_;
v___y_2411_ = v___x_2438_;
goto v___jp_2409_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v_a_2406_);
lean_dec(v_a_2404_);
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v_a_2443_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2407_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2407_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec(v_a_2404_);
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v_a_2451_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2405_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2405_);
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
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v_a_2459_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2403_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2403_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
v___jp_2380_:
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
lean_inc_ref(v___x_2379_);
v___x_2392_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2355_, v___x_2379_);
v___x_2393_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2392_);
lean_dec_ref(v___x_2392_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v___x_2394_ = lean_box(0);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2394_);
v___x_2396_ = v___x_2373_;
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
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_del_object(v___x_2373_);
v___x_2398_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2398_, 0, v_c_2356_);
lean_ctor_set(v___x_2398_, 1, v_e_2357_);
lean_ctor_set(v___x_2398_, 2, v_u_2353_);
lean_ctor_set(v___x_2398_, 3, v_v_2354_);
lean_ctor_set(v___x_2398_, 4, v_k_2355_);
lean_ctor_set(v___x_2398_, 5, v___x_2379_);
v___x_2399_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2398_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2399_;
}
}
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v___x_2467_ = lean_box(0);
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 0, v___x_2467_);
v___x_2469_ = v___x_2373_;
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
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_e_2357_);
lean_dec_ref(v_c_2356_);
lean_dec_ref(v_k_2355_);
lean_dec(v_v_2354_);
lean_dec(v_u_2353_);
v_a_2472_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2370_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2370_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2480_ = _args[0];
lean_object* v_v_2481_ = _args[1];
lean_object* v_k_2482_ = _args[2];
lean_object* v_c_2483_ = _args[3];
lean_object* v_e_2484_ = _args[4];
lean_object* v_a_2485_ = _args[5];
lean_object* v_a_2486_ = _args[6];
lean_object* v_a_2487_ = _args[7];
lean_object* v_a_2488_ = _args[8];
lean_object* v_a_2489_ = _args[9];
lean_object* v_a_2490_ = _args[10];
lean_object* v_a_2491_ = _args[11];
lean_object* v_a_2492_ = _args[12];
lean_object* v_a_2493_ = _args[13];
lean_object* v_a_2494_ = _args[14];
lean_object* v_a_2495_ = _args[15];
lean_object* v_a_2496_ = _args[16];
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2480_, v_v_2481_, v_k_2482_, v_c_2483_, v_e_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
lean_dec(v_a_2495_);
lean_dec_ref(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec(v_a_2485_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v___x_2514_; 
v_fst_2512_ = lean_ctor_get(v_x_2499_, 0);
lean_inc(v_fst_2512_);
v_snd_2513_ = lean_ctor_get(v_x_2499_, 1);
lean_inc(v_snd_2513_);
lean_dec_ref(v_x_2499_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___y_2508_);
lean_inc_ref(v___y_2507_);
lean_inc(v___y_2506_);
lean_inc_ref(v___y_2505_);
lean_inc(v___y_2504_);
lean_inc_ref(v___y_2503_);
lean_inc(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc(v___y_2500_);
v___x_2514_ = lean_apply_14(v_f_2498_, v_fst_2512_, v_snd_2513_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, lean_box(0));
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2515_, lean_object* v_x_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2515_, v_x_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec(v___y_2517_);
return v_res_2529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___f_2534_; 
v___x_2533_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2534_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2534_, 0, v___x_2533_);
return v___f_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2535_; lean_object* v___f_2536_; 
v___f_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2536_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2536_, 0, v___f_2535_);
lean_closure_set(v___f_2536_, 1, v___f_2535_);
return v___f_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2537_, lean_object* v_v_2538_, lean_object* v_f_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___x_2552_; lean_object* v_toApplicative_2553_; lean_object* v_toFunctor_2554_; lean_object* v_toSeq_2555_; lean_object* v_toSeqLeft_2556_; lean_object* v_toSeqRight_2557_; lean_object* v___f_2558_; lean_object* v___f_2559_; lean_object* v___f_2560_; lean_object* v___f_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___f_2564_; lean_object* v___f_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v_toApplicative_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2630_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2553_ = lean_ctor_get(v___x_2552_, 0);
v_toFunctor_2554_ = lean_ctor_get(v_toApplicative_2553_, 0);
v_toSeq_2555_ = lean_ctor_get(v_toApplicative_2553_, 2);
v_toSeqLeft_2556_ = lean_ctor_get(v_toApplicative_2553_, 3);
v_toSeqRight_2557_ = lean_ctor_get(v_toApplicative_2553_, 4);
v___f_2558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2554_, 2);
v___f_2560_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2560_, 0, v_toFunctor_2554_);
v___f_2561_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2561_, 0, v_toFunctor_2554_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___f_2560_);
lean_ctor_set(v___x_2562_, 1, v___f_2561_);
lean_inc(v_toSeqRight_2557_);
v___f_2563_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2563_, 0, v_toSeqRight_2557_);
lean_inc(v_toSeqLeft_2556_);
v___f_2564_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2564_, 0, v_toSeqLeft_2556_);
lean_inc(v_toSeq_2555_);
v___f_2565_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2565_, 0, v_toSeq_2555_);
v___x_2566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2562_);
lean_ctor_set(v___x_2566_, 1, v___f_2558_);
lean_ctor_set(v___x_2566_, 2, v___f_2565_);
lean_ctor_set(v___x_2566_, 3, v___f_2564_);
lean_ctor_set(v___x_2566_, 4, v___f_2563_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v___f_2559_);
v___x_2568_ = l_StateRefT_x27_instMonad___redArg(v___x_2567_);
v_toApplicative_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2568_, 1);
lean_dec(v_unused_2631_);
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2630_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_toApplicative_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2630_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v_toFunctor_2573_; lean_object* v_toSeq_2574_; lean_object* v_toSeqLeft_2575_; lean_object* v_toSeqRight_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2628_; 
v_toFunctor_2573_ = lean_ctor_get(v_toApplicative_2569_, 0);
v_toSeq_2574_ = lean_ctor_get(v_toApplicative_2569_, 2);
v_toSeqLeft_2575_ = lean_ctor_get(v_toApplicative_2569_, 3);
v_toSeqRight_2576_ = lean_ctor_get(v_toApplicative_2569_, 4);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_toApplicative_2569_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; 
v_unused_2629_ = lean_ctor_get(v_toApplicative_2569_, 1);
lean_dec(v_unused_2629_);
v___x_2578_ = v_toApplicative_2569_;
v_isShared_2579_ = v_isSharedCheck_2628_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_toSeqRight_2576_);
lean_inc(v_toSeqLeft_2575_);
lean_inc(v_toSeq_2574_);
lean_inc(v_toFunctor_2573_);
lean_dec(v_toApplicative_2569_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2628_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___f_2580_; lean_object* v___f_2581_; lean_object* v___f_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___f_2587_; lean_object* v___x_2589_; 
v___f_2580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2573_);
v___f_2582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2582_, 0, v_toFunctor_2573_);
v___f_2583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2583_, 0, v_toFunctor_2573_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___f_2582_);
lean_ctor_set(v___x_2584_, 1, v___f_2583_);
v___f_2585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2585_, 0, v_toSeqRight_2576_);
v___f_2586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2586_, 0, v_toSeqLeft_2575_);
v___f_2587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2587_, 0, v_toSeq_2574_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 4, v___f_2585_);
lean_ctor_set(v___x_2578_, 3, v___f_2586_);
lean_ctor_set(v___x_2578_, 2, v___f_2587_);
lean_ctor_set(v___x_2578_, 1, v___f_2580_);
lean_ctor_set(v___x_2578_, 0, v___x_2584_);
v___x_2589_ = v___x_2578_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___f_2580_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v___f_2587_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v___f_2586_);
lean_ctor_set(v_reuseFailAlloc_2627_, 4, v___f_2585_);
v___x_2589_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
lean_object* v___x_2591_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v___f_2581_);
lean_ctor_set(v___x_2571_, 0, v___x_2589_);
v___x_2591_ = v___x_2571_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v___f_2581_);
v___x_2591_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; 
v___x_2592_ = l_StateRefT_x27_instMonad___redArg(v___x_2591_);
v___x_2593_ = l_ReaderT_instMonad___redArg(v___x_2592_);
v___x_2594_ = l_StateRefT_x27_instMonad___redArg(v___x_2593_);
v___x_2595_ = l_ReaderT_instMonad___redArg(v___x_2594_);
v___x_2596_ = l_ReaderT_instMonad___redArg(v___x_2595_);
v___x_2597_ = l_StateRefT_x27_instMonad___redArg(v___x_2596_);
v___x_2598_ = l_ReaderT_instMonad___redArg(v___x_2597_);
v___f_2599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2600_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2617_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2603_ = v___x_2600_;
v_isShared_2604_ = v_isSharedCheck_2617_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2617_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___f_2605_; lean_object* v_cnstrsOf_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___f_2605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2606_ = lean_ctor_get(v_a_2601_, 17);
lean_inc_ref(v_cnstrsOf_2606_);
lean_dec(v_a_2601_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v_u_2537_);
lean_ctor_set(v___x_2607_, 1, v_v_2538_);
v___x_2608_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2605_, v___f_2599_, v_cnstrsOf_2606_, v___x_2607_);
lean_dec_ref(v_cnstrsOf_2606_);
if (lean_obj_tag(v___x_2608_) == 1)
{
lean_object* v_val_2609_; lean_object* v___f_2610_; lean_object* v___x_1495__overap_2611_; lean_object* v___x_2612_; 
lean_del_object(v___x_2603_);
v_val_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_val_2609_);
lean_dec_ref(v___x_2608_);
v___f_2610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2610_, 0, v_f_2539_);
v___x_1495__overap_2611_ = l_List_forM___redArg(v___x_2598_, v_val_2609_, v___f_2610_);
lean_inc(v_a_2550_);
lean_inc_ref(v_a_2549_);
lean_inc(v_a_2548_);
lean_inc_ref(v_a_2547_);
lean_inc(v_a_2546_);
lean_inc_ref(v_a_2545_);
lean_inc(v_a_2544_);
lean_inc_ref(v_a_2543_);
lean_inc(v_a_2542_);
lean_inc(v_a_2541_);
lean_inc(v_a_2540_);
v___x_2612_ = lean_apply_12(v___x_1495__overap_2611_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, lean_box(0));
return v___x_2612_;
}
else
{
lean_object* v___x_2613_; lean_object* v___x_2615_; 
lean_dec(v___x_2608_);
lean_dec_ref(v___x_2598_);
lean_dec_ref(v_f_2539_);
v___x_2613_ = lean_box(0);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2613_);
v___x_2615_ = v___x_2603_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v___x_2598_);
lean_dec_ref(v_f_2539_);
lean_dec(v_v_2538_);
lean_dec(v_u_2537_);
v_a_2618_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2600_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2600_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2632_, lean_object* v_v_2633_, lean_object* v_f_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2632_, v_v_2633_, v_f_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec(v_a_2635_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2649_, v_a_2650_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2675_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2655_ = v___x_2652_;
v_isShared_2656_ = v_isSharedCheck_2675_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2652_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2675_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_termMapInv_2657_; lean_object* v___x_2658_; 
v_termMapInv_2657_ = lean_ctor_get(v_a_2653_, 4);
lean_inc_ref(v_termMapInv_2657_);
lean_dec(v_a_2653_);
v___x_2658_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2657_, v_e_2648_);
lean_dec_ref(v_termMapInv_2657_);
if (lean_obj_tag(v___x_2658_) == 1)
{
lean_object* v_val_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2670_; 
v_val_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_val_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2670_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_fst_2663_; lean_object* v___x_2665_; 
v_fst_2663_ = lean_ctor_get(v_val_2659_, 0);
lean_inc(v_fst_2663_);
lean_dec(v_val_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v_fst_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_fst_2663_);
v___x_2665_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2665_);
v___x_2667_ = v___x_2655_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_dec(v___x_2658_);
v___x_2671_ = lean_box(0);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2671_);
v___x_2673_ = v___x_2655_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2652_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2652_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2652_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2652_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2684_, v_a_2685_, v_a_2686_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_e_2684_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2689_, v_a_2690_, v_a_2698_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
lean_dec(v_a_2712_);
lean_dec_ref(v_a_2711_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec_ref(v_e_2702_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2715_, lean_object* v_v_2716_, lean_object* v_k_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___y_2731_; lean_object* v___y_2732_; lean_object* v___y_2733_; uint8_t v___x_2773_; 
v___x_2773_ = lean_nat_dec_eq(v_u_2715_, v_v_2716_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2911_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2911_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2911_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
uint8_t v___x_2784_; 
v___x_2784_ = lean_unbox(v_a_2775_);
lean_dec(v_a_2775_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2777_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
else
{
uint8_t v___x_2787_; 
v___x_2787_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2717_);
if (v___x_2787_ == 0)
{
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
goto v___jp_2779_;
}
else
{
if (v___x_2773_ == 0)
{
lean_object* v___x_2788_; 
lean_del_object(v___x_2777_);
v___x_2788_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_2716_, v_u_2715_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2902_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2902_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2902_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
if (lean_obj_tag(v_a_2789_) == 1)
{
lean_object* v_val_2793_; uint8_t v___x_2794_; 
v_val_2793_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_val_2793_);
lean_dec_ref(v_a_2789_);
v___x_2794_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2793_);
lean_dec(v_val_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; lean_object* v___x_2797_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2795_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2795_);
v___x_2797_ = v___x_2791_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
else
{
lean_object* v___x_2799_; 
lean_del_object(v___x_2791_);
v___x_2799_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2715_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v___x_2801_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2716_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___y_2804_; lean_object* v___x_2878_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref(v___x_2801_);
v___x_2878_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2800_, v_a_2719_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; uint8_t v___x_2880_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
v___x_2880_ = lean_unbox(v_a_2879_);
lean_dec(v_a_2879_);
if (v___x_2880_ == 0)
{
v___y_2804_ = v___x_2878_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2881_; 
lean_dec_ref(v___x_2878_);
v___x_2881_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2802_, v_a_2719_);
v___y_2804_ = v___x_2881_;
goto v___jp_2803_;
}
}
else
{
v___y_2804_ = v___x_2878_;
goto v___jp_2803_;
}
v___jp_2803_:
{
if (lean_obj_tag(v___y_2804_) == 0)
{
lean_object* v_a_2805_; uint8_t v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___y_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref(v___y_2804_);
v___x_2806_ = lean_unbox(v_a_2805_);
lean_dec(v_a_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2800_, v_a_2719_, v_a_2727_);
lean_dec(v_a_2800_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2840_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2810_ = v___x_2807_;
v_isShared_2811_ = v_isSharedCheck_2840_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2807_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2840_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
if (lean_obj_tag(v_a_2808_) == 1)
{
lean_object* v_val_2812_; lean_object* v___x_2813_; 
lean_del_object(v___x_2810_);
v_val_2812_ = lean_ctor_get(v_a_2808_, 0);
lean_inc(v_val_2812_);
lean_dec_ref(v_a_2808_);
v___x_2813_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2802_, v_a_2719_, v_a_2727_);
lean_dec(v_a_2802_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2827_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2816_ = v___x_2813_;
v_isShared_2817_ = v_isSharedCheck_2827_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2813_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2827_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
if (lean_obj_tag(v_a_2814_) == 1)
{
lean_object* v_val_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2816_);
v_val_2818_ = lean_ctor_get(v_a_2814_, 0);
lean_inc(v_val_2818_);
lean_dec_ref(v_a_2814_);
v___x_2819_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2812_, v_a_2719_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v_a_2820_; uint8_t v___x_2821_; 
v_a_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_a_2820_);
v___x_2821_ = lean_unbox(v_a_2820_);
lean_dec(v_a_2820_);
if (v___x_2821_ == 0)
{
v___y_2731_ = v_val_2818_;
v___y_2732_ = v_val_2812_;
v___y_2733_ = v___x_2819_;
goto v___jp_2730_;
}
else
{
lean_object* v___x_2822_; 
lean_dec_ref(v___x_2819_);
v___x_2822_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2818_, v_a_2719_);
v___y_2731_ = v_val_2818_;
v___y_2732_ = v_val_2812_;
v___y_2733_ = v___x_2822_;
goto v___jp_2730_;
}
}
else
{
v___y_2731_ = v_val_2818_;
v___y_2732_ = v_val_2812_;
v___y_2733_ = v___x_2819_;
goto v___jp_2730_;
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2825_; 
lean_dec(v_a_2814_);
lean_dec(v_val_2812_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2823_ = lean_box(0);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2823_);
v___x_2825_ = v___x_2816_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_val_2812_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2828_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2813_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2813_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_dec(v_a_2808_);
lean_dec(v_a_2802_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2836_ = lean_box(0);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 0, v___x_2836_);
v___x_2838_ = v___x_2810_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
else
{
lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2848_; 
lean_dec(v_a_2802_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2841_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2807_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2807_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2846_; 
if (v_isShared_2844_ == 0)
{
v___x_2846_ = v___x_2843_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_a_2841_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2800_, v_a_2802_, v_a_2719_);
lean_dec(v_a_2802_);
lean_dec(v_a_2800_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2861_; 
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2861_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_unbox(v_a_2850_);
lean_dec(v_a_2850_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_del_object(v___x_2852_);
v___x_2855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2855_, 0, v_u_2715_);
lean_ctor_set(v___x_2855_, 1, v_v_2716_);
v___x_2856_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2855_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
return v___x_2856_;
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2857_ = lean_box(0);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2857_);
v___x_2859_ = v___x_2852_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2862_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2849_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2849_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2802_);
lean_dec(v_a_2800_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2870_ = lean_ctor_get(v___y_2804_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___y_2804_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___y_2804_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___y_2804_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec(v_a_2800_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2882_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2801_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2801_);
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
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2890_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2799_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2799_);
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
lean_object* v___x_2898_; lean_object* v___x_2900_; 
lean_dec(v_a_2789_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2898_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2898_);
v___x_2900_ = v___x_2791_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2903_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2788_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2788_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
goto v___jp_2779_;
}
}
}
v___jp_2779_:
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(0);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2780_);
v___x_2782_ = v___x_2777_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2912_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2774_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2774_);
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
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
return v___x_2921_;
}
v___jp_2730_:
{
if (lean_obj_tag(v___y_2733_) == 0)
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2764_; 
v_a_2734_ = lean_ctor_get(v___y_2733_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___y_2733_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2736_ = v___y_2733_;
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___y_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint8_t v___x_2738_; 
v___x_2738_ = lean_unbox(v_a_2734_);
lean_dec(v_a_2734_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2739_ = lean_box(0);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2739_);
v___x_2741_ = v___x_2736_;
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
else
{
lean_object* v___x_2743_; 
lean_del_object(v___x_2736_);
v___x_2743_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2732_, v___y_2731_, v_a_2719_);
lean_dec_ref(v___y_2731_);
lean_dec_ref(v___y_2732_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2755_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v___x_2748_; 
v___x_2748_ = lean_unbox(v_a_2744_);
lean_dec(v_a_2744_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_del_object(v___x_2746_);
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_u_2715_);
lean_ctor_set(v___x_2749_, 1, v_v_2716_);
v___x_2750_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2749_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v___x_2751_ = lean_box(0);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2751_);
v___x_2753_ = v___x_2746_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2756_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2743_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2743_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec_ref(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_v_2716_);
lean_dec(v_u_2715_);
v_a_2765_ = lean_ctor_get(v___y_2733_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___y_2733_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___y_2733_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___y_2733_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2922_, lean_object* v_v_2923_, lean_object* v_k_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2922_, v_v_2923_, v_k_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec_ref(v_a_2930_);
lean_dec(v_a_2929_);
lean_dec_ref(v_a_2928_);
lean_dec(v_a_2927_);
lean_dec(v_a_2926_);
lean_dec(v_a_2925_);
lean_dec_ref(v_k_2924_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2938_, lean_object* v_vals_2939_, lean_object* v_i_2940_, lean_object* v_k_2941_){
_start:
{
uint8_t v___y_2943_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = lean_array_get_size(v_keys_2938_);
v___x_2950_ = lean_nat_dec_lt(v_i_2940_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_i_2940_);
v___x_2951_ = lean_box(0);
return v___x_2951_;
}
else
{
lean_object* v_fst_2952_; lean_object* v_snd_2953_; lean_object* v_k_x27_2954_; lean_object* v_fst_2955_; lean_object* v_snd_2956_; uint8_t v___x_2957_; 
v_fst_2952_ = lean_ctor_get(v_k_2941_, 0);
v_snd_2953_ = lean_ctor_get(v_k_2941_, 1);
v_k_x27_2954_ = lean_array_fget_borrowed(v_keys_2938_, v_i_2940_);
v_fst_2955_ = lean_ctor_get(v_k_x27_2954_, 0);
v_snd_2956_ = lean_ctor_get(v_k_x27_2954_, 1);
v___x_2957_ = lean_nat_dec_eq(v_fst_2952_, v_fst_2955_);
if (v___x_2957_ == 0)
{
v___y_2943_ = v___x_2957_;
goto v___jp_2942_;
}
else
{
uint8_t v___x_2958_; 
v___x_2958_ = lean_nat_dec_eq(v_snd_2953_, v_snd_2956_);
v___y_2943_ = v___x_2958_;
goto v___jp_2942_;
}
}
v___jp_2942_:
{
if (v___y_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_unsigned_to_nat(1u);
v___x_2945_ = lean_nat_add(v_i_2940_, v___x_2944_);
lean_dec(v_i_2940_);
v_i_2940_ = v___x_2945_;
goto _start;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_array_fget_borrowed(v_vals_2939_, v_i_2940_);
lean_dec(v_i_2940_);
lean_inc(v___x_2947_);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2959_, lean_object* v_vals_2960_, lean_object* v_i_2961_, lean_object* v_k_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2959_, v_vals_2960_, v_i_2961_, v_k_2962_);
lean_dec_ref(v_k_2962_);
lean_dec_ref(v_vals_2960_);
lean_dec_ref(v_keys_2959_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2964_, size_t v_x_2965_, lean_object* v_x_2966_){
_start:
{
if (lean_obj_tag(v_x_2964_) == 0)
{
lean_object* v_es_2967_; lean_object* v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; lean_object* v_j_2972_; lean_object* v___x_2973_; 
v_es_2967_ = lean_ctor_get(v_x_2964_, 0);
v___x_2968_ = lean_box(2);
v___x_2969_ = ((size_t)5ULL);
v___x_2970_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1);
v___x_2971_ = lean_usize_land(v_x_2965_, v___x_2970_);
v_j_2972_ = lean_usize_to_nat(v___x_2971_);
v___x_2973_ = lean_array_get_borrowed(v___x_2968_, v_es_2967_, v_j_2972_);
lean_dec(v_j_2972_);
switch(lean_obj_tag(v___x_2973_))
{
case 0:
{
lean_object* v_key_2974_; lean_object* v_val_2975_; uint8_t v___y_2977_; lean_object* v_fst_2980_; lean_object* v_snd_2981_; lean_object* v_fst_2982_; lean_object* v_snd_2983_; uint8_t v___x_2984_; 
v_key_2974_ = lean_ctor_get(v___x_2973_, 0);
v_val_2975_ = lean_ctor_get(v___x_2973_, 1);
v_fst_2980_ = lean_ctor_get(v_x_2966_, 0);
v_snd_2981_ = lean_ctor_get(v_x_2966_, 1);
v_fst_2982_ = lean_ctor_get(v_key_2974_, 0);
v_snd_2983_ = lean_ctor_get(v_key_2974_, 1);
v___x_2984_ = lean_nat_dec_eq(v_fst_2980_, v_fst_2982_);
if (v___x_2984_ == 0)
{
v___y_2977_ = v___x_2984_;
goto v___jp_2976_;
}
else
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_eq(v_snd_2981_, v_snd_2983_);
v___y_2977_ = v___x_2985_;
goto v___jp_2976_;
}
v___jp_2976_:
{
if (v___y_2977_ == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = lean_box(0);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; 
lean_inc(v_val_2975_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_val_2975_);
return v___x_2979_;
}
}
}
case 1:
{
lean_object* v_node_2986_; size_t v___x_2987_; 
v_node_2986_ = lean_ctor_get(v___x_2973_, 0);
v___x_2987_ = lean_usize_shift_right(v_x_2965_, v___x_2969_);
v_x_2964_ = v_node_2986_;
v_x_2965_ = v___x_2987_;
goto _start;
}
default: 
{
lean_object* v___x_2989_; 
v___x_2989_ = lean_box(0);
return v___x_2989_;
}
}
}
else
{
lean_object* v_ks_2990_; lean_object* v_vs_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_ks_2990_ = lean_ctor_get(v_x_2964_, 0);
v_vs_2991_ = lean_ctor_get(v_x_2964_, 1);
v___x_2992_ = lean_unsigned_to_nat(0u);
v___x_2993_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_2990_, v_vs_2991_, v___x_2992_, v_x_2966_);
return v___x_2993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_){
_start:
{
size_t v_x_3958__boxed_2997_; lean_object* v_res_2998_; 
v_x_3958__boxed_2997_ = lean_unbox_usize(v_x_2995_);
lean_dec(v_x_2995_);
v_res_2998_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2994_, v_x_3958__boxed_2997_, v_x_2996_);
lean_dec_ref(v_x_2996_);
lean_dec_ref(v_x_2994_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_fst_3001_; lean_object* v_snd_3002_; uint64_t v___x_3003_; uint64_t v___x_3004_; uint64_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v_fst_3001_ = lean_ctor_get(v_x_3000_, 0);
v_snd_3002_ = lean_ctor_get(v_x_3000_, 1);
v___x_3003_ = lean_uint64_of_nat(v_fst_3001_);
v___x_3004_ = lean_uint64_of_nat(v_snd_3002_);
v___x_3005_ = lean_uint64_mix_hash(v___x_3003_, v___x_3004_);
v___x_3006_ = lean_uint64_to_usize(v___x_3005_);
v___x_3007_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2999_, v___x_3006_, v_x_3000_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3008_, lean_object* v_x_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3008_, v_x_3009_);
lean_dec_ref(v_x_3009_);
lean_dec_ref(v_x_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3011_, lean_object* v_v_3012_, lean_object* v_k_3013_, lean_object* v_as_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
if (lean_obj_tag(v_as_3014_) == 0)
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v_k_3013_);
lean_dec(v_v_3012_);
lean_dec(v_u_3011_);
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
else
{
lean_object* v_head_3029_; lean_object* v_tail_3030_; lean_object* v_fst_3031_; lean_object* v_snd_3032_; lean_object* v___x_3033_; 
v_head_3029_ = lean_ctor_get(v_as_3014_, 0);
lean_inc(v_head_3029_);
v_tail_3030_ = lean_ctor_get(v_as_3014_, 1);
lean_inc(v_tail_3030_);
lean_dec_ref(v_as_3014_);
v_fst_3031_ = lean_ctor_get(v_head_3029_, 0);
lean_inc(v_fst_3031_);
v_snd_3032_ = lean_ctor_get(v_head_3029_, 1);
lean_inc(v_snd_3032_);
lean_dec(v_head_3029_);
lean_inc_ref(v_k_3013_);
lean_inc(v_v_3012_);
lean_inc(v_u_3011_);
v___x_3033_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3011_, v_v_3012_, v_k_3013_, v_fst_3031_, v_snd_3032_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec_ref(v___x_3033_);
v_as_3014_ = v_tail_3030_;
goto _start;
}
else
{
lean_dec(v_tail_3030_);
lean_dec_ref(v_k_3013_);
lean_dec(v_v_3012_);
lean_dec(v_u_3011_);
return v___x_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3035_, lean_object* v_v_3036_, lean_object* v_k_3037_, lean_object* v_as_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3035_, v_v_3036_, v_k_3037_, v_as_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec(v___y_3039_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3052_, lean_object* v_v_3053_, lean_object* v_k_3054_, lean_object* v_as_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
if (lean_obj_tag(v_as_3055_) == 0)
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec_ref(v_k_3054_);
lean_dec(v_v_3053_);
lean_dec(v_u_3052_);
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3068_);
return v___x_3069_;
}
else
{
lean_object* v_head_3070_; lean_object* v_tail_3071_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___x_3074_; 
v_head_3070_ = lean_ctor_get(v_as_3055_, 0);
lean_inc(v_head_3070_);
v_tail_3071_ = lean_ctor_get(v_as_3055_, 1);
lean_inc(v_tail_3071_);
lean_dec_ref(v_as_3055_);
v_fst_3072_ = lean_ctor_get(v_head_3070_, 0);
lean_inc(v_fst_3072_);
v_snd_3073_ = lean_ctor_get(v_head_3070_, 1);
lean_inc(v_snd_3073_);
lean_dec(v_head_3070_);
lean_inc_ref(v_k_3054_);
lean_inc(v_v_3053_);
lean_inc(v_u_3052_);
v___x_3074_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3052_, v_v_3053_, v_k_3054_, v_fst_3072_, v_snd_3073_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_dec_ref(v___x_3074_);
v_as_3055_ = v_tail_3071_;
goto _start;
}
else
{
lean_dec(v_tail_3071_);
lean_dec_ref(v_k_3054_);
lean_dec(v_v_3053_);
lean_dec(v_u_3052_);
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3076_, lean_object* v_v_3077_, lean_object* v_k_3078_, lean_object* v_as_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3076_, v_v_3077_, v_k_3078_, v_as_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3093_, lean_object* v_v_3094_, lean_object* v_k_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_cnstrsOf_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref(v___x_3126_);
v_cnstrsOf_3128_ = lean_ctor_get(v_a_3127_, 17);
lean_inc_ref(v_cnstrsOf_3128_);
lean_dec(v_a_3127_);
lean_inc(v_v_3094_);
lean_inc(v_u_3093_);
v___x_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3129_, 0, v_u_3093_);
lean_ctor_set(v___x_3129_, 1, v_v_3094_);
v___x_3130_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3128_, v___x_3129_);
lean_dec_ref(v___x_3129_);
lean_dec_ref(v_cnstrsOf_3128_);
if (lean_obj_tag(v___x_3130_) == 1)
{
lean_object* v_val_3131_; lean_object* v___x_3132_; 
v_val_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_val_3131_);
lean_dec_ref(v___x_3130_);
lean_inc_ref(v_k_3095_);
lean_inc(v_v_3094_);
lean_inc(v_u_3093_);
v___x_3132_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3093_, v_v_3094_, v_k_3095_, v_val_3131_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_dec_ref(v___x_3132_);
goto v___jp_3108_;
}
else
{
lean_dec_ref(v_k_3095_);
lean_dec(v_v_3094_);
lean_dec(v_u_3093_);
return v___x_3132_;
}
}
else
{
lean_dec(v___x_3130_);
goto v___jp_3108_;
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v_k_3095_);
lean_dec(v_v_3094_);
lean_dec(v_u_3093_);
v_a_3133_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3126_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3126_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
v___jp_3108_:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v_cnstrsOf_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_a_3110_);
lean_dec_ref(v___x_3109_);
v_cnstrsOf_3111_ = lean_ctor_get(v_a_3110_, 17);
lean_inc_ref(v_cnstrsOf_3111_);
lean_dec(v_a_3110_);
lean_inc(v_u_3093_);
lean_inc(v_v_3094_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_v_3094_);
lean_ctor_set(v___x_3112_, 1, v_u_3093_);
v___x_3113_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3111_, v___x_3112_);
lean_dec_ref(v___x_3112_);
lean_dec_ref(v_cnstrsOf_3111_);
if (lean_obj_tag(v___x_3113_) == 1)
{
lean_object* v_val_3114_; lean_object* v___x_3115_; 
v_val_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_val_3114_);
lean_dec_ref(v___x_3113_);
lean_inc_ref(v_k_3095_);
lean_inc(v_v_3094_);
lean_inc(v_u_3093_);
v___x_3115_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3093_, v_v_3094_, v_k_3095_, v_val_3114_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v___x_3116_; 
lean_dec_ref(v___x_3115_);
v___x_3116_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3093_, v_v_3094_, v_k_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
lean_dec_ref(v_k_3095_);
return v___x_3116_;
}
else
{
lean_dec_ref(v_k_3095_);
lean_dec(v_v_3094_);
lean_dec(v_u_3093_);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3117_; 
lean_dec(v___x_3113_);
v___x_3117_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3093_, v_v_3094_, v_k_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_);
lean_dec_ref(v_k_3095_);
return v___x_3117_;
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec_ref(v_k_3095_);
lean_dec(v_v_3094_);
lean_dec(v_u_3093_);
v_a_3118_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3109_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3109_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3141_, lean_object* v_v_3142_, lean_object* v_k_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3141_, v_v_3142_, v_k_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec(v_a_3145_);
lean_dec(v_a_3144_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3158_, v_x_3159_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3161_, lean_object* v_x_3162_, lean_object* v_x_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3161_, v_x_3162_, v_x_3163_);
lean_dec_ref(v_x_3163_);
lean_dec_ref(v_x_3162_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3165_, lean_object* v_x_3166_, size_t v_x_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3166_, v_x_3167_, v_x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
size_t v_x_4226__boxed_3174_; lean_object* v_res_3175_; 
v_x_4226__boxed_3174_ = lean_unbox_usize(v_x_3172_);
lean_dec(v_x_3172_);
v_res_3175_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3170_, v_x_3171_, v_x_4226__boxed_3174_, v_x_3173_);
lean_dec_ref(v_x_3173_);
lean_dec_ref(v_x_3171_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3176_, lean_object* v_keys_3177_, lean_object* v_vals_3178_, lean_object* v_heq_3179_, lean_object* v_i_3180_, lean_object* v_k_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3177_, v_vals_3178_, v_i_3180_, v_k_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3183_, lean_object* v_keys_3184_, lean_object* v_vals_3185_, lean_object* v_heq_3186_, lean_object* v_i_3187_, lean_object* v_k_3188_){
_start:
{
lean_object* v_res_3189_; 
v_res_3189_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3183_, v_keys_3184_, v_vals_3185_, v_heq_3186_, v_i_3187_, v_k_3188_);
lean_dec_ref(v_k_3188_);
lean_dec_ref(v_vals_3185_);
lean_dec_ref(v_keys_3184_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3190_, lean_object* v_v_3191_, lean_object* v_k_3192_, lean_object* v_w_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3190_, v_v_3191_, v_k_3192_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3229_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3229_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3229_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
uint8_t v___x_3211_; 
v___x_3211_ = lean_unbox(v_a_3207_);
lean_dec(v_a_3207_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3214_; 
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
v___x_3212_ = lean_box(0);
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3212_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
else
{
lean_object* v___x_3216_; 
lean_del_object(v___x_3209_);
lean_inc_ref(v_k_3192_);
lean_inc(v_v_3191_);
lean_inc(v_u_3190_);
v___x_3216_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3190_, v_v_3191_, v_k_3192_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3217_; 
lean_dec_ref(v___x_3216_);
v___x_3217_ = l_Lean_Meta_Grind_Order_getProof(v_w_3193_, v_v_3191_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
lean_inc(v_v_3191_);
lean_inc(v_u_3190_);
v___x_3219_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3190_, v_v_3191_, v_a_3218_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v___x_3219_);
v___x_3220_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3190_, v_v_3191_, v_k_3192_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
return v___x_3220_;
}
else
{
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
return v___x_3219_;
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
v_a_3221_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3217_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3217_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
else
{
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v_k_3192_);
lean_dec(v_v_3191_);
lean_dec(v_u_3190_);
v_a_3230_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3206_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3206_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3238_, lean_object* v_v_3239_, lean_object* v_k_3240_, lean_object* v_w_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3238_, v_v_3239_, v_k_3240_, v_w_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3252_);
lean_dec_ref(v_a_3251_);
lean_dec(v_a_3250_);
lean_dec_ref(v_a_3249_);
lean_dec(v_a_3248_);
lean_dec_ref(v_a_3247_);
lean_dec(v_a_3246_);
lean_dec_ref(v_a_3245_);
lean_dec(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec(v_a_3242_);
lean_dec(v_w_3241_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3255_, lean_object* v_i_3256_, lean_object* v_v_3257_, lean_object* v_x_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_){
_start:
{
if (lean_obj_tag(v_x_3258_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3272_; 
lean_dec(v_i_3256_);
v___x_3271_ = lean_box(0);
v___x_3272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
return v___x_3272_;
}
else
{
lean_object* v_key_3273_; lean_object* v_value_3274_; lean_object* v_tail_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_key_3273_ = lean_ctor_get(v_x_3258_, 0);
lean_inc(v_key_3273_);
v_value_3274_ = lean_ctor_get(v_x_3258_, 1);
lean_inc(v_value_3274_);
v_tail_3275_ = lean_ctor_get(v_x_3258_, 2);
lean_inc(v_tail_3275_);
lean_dec_ref(v_x_3258_);
v___x_3276_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3255_, v_value_3274_);
lean_inc(v_i_3256_);
v___x_3277_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3256_, v_key_3273_, v___x_3276_, v_v_3257_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_dec_ref(v___x_3277_);
v_x_3258_ = v_tail_3275_;
goto _start;
}
else
{
lean_dec(v_tail_3275_);
lean_dec(v_i_3256_);
return v___x_3277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3279_, lean_object* v_i_3280_, lean_object* v_v_3281_, lean_object* v_x_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3279_, v_i_3280_, v_v_3281_, v_x_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec(v_v_3281_);
lean_dec_ref(v___x_3279_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3296_, lean_object* v_v_3297_, lean_object* v_u_3298_, lean_object* v_x_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
if (lean_obj_tag(v_x_3299_) == 0)
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_v_3297_);
lean_dec_ref(v_k_3296_);
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
return v___x_3313_;
}
else
{
lean_object* v_key_3314_; lean_object* v_value_3315_; lean_object* v_tail_3316_; lean_object* v___y_3318_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v_key_3314_ = lean_ctor_get(v_x_3299_, 0);
lean_inc_n(v_key_3314_, 2);
v_value_3315_ = lean_ctor_get(v_x_3299_, 1);
lean_inc(v_value_3315_);
v_tail_3316_ = lean_ctor_get(v_x_3299_, 2);
lean_inc(v_tail_3316_);
lean_dec_ref(v_x_3299_);
lean_inc_ref(v_k_3296_);
v___x_3320_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3315_, v_k_3296_);
lean_dec(v_value_3315_);
lean_inc_ref(v___x_3320_);
lean_inc(v_v_3297_);
v___x_3321_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3314_, v_v_3297_, v___x_3320_, v_u_3298_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3321_) == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v___x_3321_);
v___x_3322_ = l_Lean_Meta_Grind_Order_getStruct(v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v_targets_3324_; lean_object* v_size_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
v_targets_3324_ = lean_ctor_get(v_a_3323_, 19);
lean_inc_ref(v_targets_3324_);
lean_dec(v_a_3323_);
v_size_3325_ = lean_ctor_get(v_targets_3324_, 2);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_nat_dec_lt(v_v_3297_, v_size_3325_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec_ref(v_targets_3324_);
v___x_3328_ = l_outOfBounds___redArg(v___x_3326_);
v___x_3329_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3320_, v_key_3314_, v_v_3297_, v___x_3328_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec_ref(v___x_3320_);
v___y_3318_ = v___x_3329_;
goto v___jp_3317_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3330_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3326_, v_targets_3324_, v_v_3297_);
lean_dec_ref(v_targets_3324_);
v___x_3331_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3320_, v_key_3314_, v_v_3297_, v___x_3330_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec_ref(v___x_3320_);
v___y_3318_ = v___x_3331_;
goto v___jp_3317_;
}
}
else
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
lean_dec_ref(v___x_3320_);
lean_dec(v_tail_3316_);
lean_dec(v_key_3314_);
lean_dec(v_v_3297_);
lean_dec_ref(v_k_3296_);
v_a_3332_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___x_3322_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3322_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3337_; 
if (v_isShared_3335_ == 0)
{
v___x_3337_ = v___x_3334_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v_a_3332_);
v___x_3337_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
return v___x_3337_;
}
}
}
}
else
{
lean_dec_ref(v___x_3320_);
lean_dec(v_key_3314_);
v___y_3318_ = v___x_3321_;
goto v___jp_3317_;
}
v___jp_3317_:
{
if (lean_obj_tag(v___y_3318_) == 0)
{
lean_dec_ref(v___y_3318_);
v_x_3299_ = v_tail_3316_;
goto _start;
}
else
{
lean_dec(v_tail_3316_);
lean_dec(v_v_3297_);
lean_dec_ref(v_k_3296_);
return v___y_3318_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3340_, lean_object* v_v_3341_, lean_object* v_u_3342_, lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3340_, v_v_3341_, v_u_3342_, v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
lean_dec(v___y_3354_);
lean_dec_ref(v___y_3353_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec(v_u_3342_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3357_, lean_object* v_v_3358_, lean_object* v_k_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___y_3373_; lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v_targets_3394_; lean_object* v_size_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref(v___x_3392_);
v_targets_3394_ = lean_ctor_get(v_a_3393_, 19);
lean_inc_ref(v_targets_3394_);
lean_dec(v_a_3393_);
v_size_3395_ = lean_ctor_get(v_targets_3394_, 2);
v___x_3396_ = lean_box(0);
v___x_3397_ = lean_nat_dec_lt(v_v_3358_, v_size_3395_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v_targets_3394_);
v___x_3398_ = l_outOfBounds___redArg(v___x_3396_);
lean_inc(v_u_3357_);
v___x_3399_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3359_, v_u_3357_, v_v_3358_, v___x_3398_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
v___y_3373_ = v___x_3399_;
goto v___jp_3372_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3396_, v_targets_3394_, v_v_3358_);
lean_dec_ref(v_targets_3394_);
lean_inc(v_u_3357_);
v___x_3401_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3359_, v_u_3357_, v_v_3358_, v___x_3400_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
v___y_3373_ = v___x_3401_;
goto v___jp_3372_;
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_k_3359_);
lean_dec(v_v_3358_);
lean_dec(v_u_3357_);
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
v___jp_3372_:
{
if (lean_obj_tag(v___y_3373_) == 0)
{
lean_object* v___x_3374_; 
lean_dec_ref(v___y_3373_);
v___x_3374_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v_sources_3376_; lean_object* v_size_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
v_sources_3376_ = lean_ctor_get(v_a_3375_, 18);
lean_inc_ref(v_sources_3376_);
lean_dec(v_a_3375_);
v_size_3377_ = lean_ctor_get(v_sources_3376_, 2);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_nat_dec_lt(v_u_3357_, v_size_3377_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v_sources_3376_);
v___x_3380_ = l_outOfBounds___redArg(v___x_3378_);
v___x_3381_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3359_, v_v_3358_, v_u_3357_, v___x_3380_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_u_3357_);
return v___x_3381_;
}
else
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3378_, v_sources_3376_, v_u_3357_);
lean_dec_ref(v_sources_3376_);
v___x_3383_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3359_, v_v_3358_, v_u_3357_, v___x_3382_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
lean_dec(v_u_3357_);
return v___x_3383_;
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_k_3359_);
lean_dec(v_v_3358_);
lean_dec(v_u_3357_);
v_a_3384_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3374_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3374_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
else
{
lean_dec_ref(v_k_3359_);
lean_dec(v_v_3358_);
lean_dec(v_u_3357_);
return v___y_3373_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3410_, lean_object* v_v_3411_, lean_object* v_k_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3410_, v_v_3411_, v_k_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec(v_a_3413_);
return v_res_3425_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3434_ = l_Lean_Name_append(v___x_3433_, v___x_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3435_, lean_object* v_v_3436_, lean_object* v_k_3437_, lean_object* v_h_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3440_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3603_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3603_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3603_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
uint8_t v___x_3531_; 
v___x_3531_ = lean_unbox(v_a_3527_);
lean_dec(v_a_3527_);
if (v___x_3531_ == 0)
{
uint8_t v___x_3532_; 
lean_del_object(v___x_3529_);
v___x_3532_ = lean_nat_dec_eq(v_u_3435_, v_v_3436_);
if (v___x_3532_ == 0)
{
lean_object* v_options_3533_; uint8_t v_hasTrace_3534_; 
v_options_3533_ = lean_ctor_get(v_a_3448_, 2);
v_hasTrace_3534_ = lean_ctor_get_uint8(v_options_3533_, sizeof(void*)*1);
if (v_hasTrace_3534_ == 0)
{
v___y_3489_ = v_a_3439_;
v___y_3490_ = v_a_3440_;
v___y_3491_ = v_a_3441_;
v___y_3492_ = v_a_3442_;
v___y_3493_ = v_a_3443_;
v___y_3494_ = v_a_3444_;
v___y_3495_ = v_a_3445_;
v___y_3496_ = v_a_3446_;
v___y_3497_ = v_a_3447_;
v___y_3498_ = v_a_3448_;
v___y_3499_ = v_a_3449_;
goto v___jp_3488_;
}
else
{
lean_object* v_inheritedTraceOptions_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_inheritedTraceOptions_3535_ = lean_ctor_get(v_a_3448_, 13);
v___x_3536_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3537_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3535_, v_options_3533_, v___x_3537_);
if (v___x_3538_ == 0)
{
v___y_3489_ = v_a_3439_;
v___y_3490_ = v_a_3440_;
v___y_3491_ = v_a_3441_;
v___y_3492_ = v_a_3442_;
v___y_3493_ = v_a_3443_;
v___y_3494_ = v_a_3444_;
v___y_3495_ = v_a_3445_;
v___y_3496_ = v_a_3446_;
v___y_3497_ = v_a_3447_;
v___y_3498_ = v_a_3448_;
v___y_3499_ = v_a_3449_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref(v___x_3539_);
v___x_3541_ = l_Lean_Meta_Grind_Order_getExpr(v_v_3436_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v_k_3543_; uint8_t v_strict_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___y_3552_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref(v___x_3541_);
v_k_3543_ = lean_ctor_get(v_k_3437_, 0);
v_strict_3544_ = lean_ctor_get_uint8(v_k_3437_, sizeof(void*)*1);
v___x_3545_ = l_Lean_MessageData_ofExpr(v_a_3540_);
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_a_3542_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___x_3546_);
if (v_strict_3544_ == 0)
{
lean_object* v___x_3557_; 
v___x_3557_ = l_Int_repr(v_k_3543_);
v___y_3552_ = v___x_3557_;
goto v___jp_3551_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = l_Int_repr(v_k_3543_);
v___x_3559_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3560_ = lean_string_append(v___x_3558_, v___x_3559_);
v___y_3552_ = v___x_3560_;
goto v___jp_3551_;
}
v___jp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___y_3552_);
v___x_3554_ = l_Lean_MessageData_ofFormat(v___x_3553_);
v___x_3555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3550_);
lean_ctor_set(v___x_3555_, 1, v___x_3554_);
v___x_3556_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3536_, v___x_3555_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref(v___x_3556_);
v___y_3489_ = v_a_3439_;
v___y_3490_ = v_a_3440_;
v___y_3491_ = v_a_3441_;
v___y_3492_ = v_a_3442_;
v___y_3493_ = v_a_3443_;
v___y_3494_ = v_a_3444_;
v___y_3495_ = v_a_3445_;
v___y_3496_ = v_a_3446_;
v___y_3497_ = v_a_3447_;
v___y_3498_ = v_a_3448_;
v___y_3499_ = v_a_3449_;
goto v___jp_3488_;
}
else
{
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
return v___x_3556_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v_a_3540_);
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v_a_3561_ = lean_ctor_get(v___x_3541_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3541_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3541_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3541_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v_a_3569_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3539_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3539_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
else
{
uint8_t v___x_3577_; 
lean_dec(v_v_3436_);
v___x_3577_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3437_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_u_3435_);
goto v___jp_3523_;
}
else
{
lean_object* v___x_3578_; 
v___x_3578_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3435_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_u_3435_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref(v___x_3578_);
v___x_3580_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3579_, v_k_3437_, v_h_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec_ref(v_k_3437_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref(v___x_3580_);
v___x_3582_ = l_Lean_Meta_Grind_closeGoal(v_a_3581_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_dec_ref(v___x_3582_);
goto v___jp_3523_;
}
else
{
return v___x_3582_;
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3580_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3580_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
v_a_3591_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3578_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3578_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v___x_3599_ = lean_box(0);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v___x_3599_);
v___x_3601_ = v___x_3529_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v_a_3604_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3526_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3526_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
v___jp_3451_:
{
lean_object* v___x_3463_; 
v___x_3463_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3435_, v_v_3436_, v_k_3437_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3479_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
uint8_t v___x_3468_; 
v___x_3468_ = lean_unbox(v_a_3464_);
lean_dec(v_a_3464_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v___x_3469_ = lean_box(0);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3469_);
v___x_3471_ = v___x_3466_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
else
{
lean_object* v___x_3473_; 
lean_del_object(v___x_3466_);
lean_inc_ref(v_k_3437_);
lean_inc(v_v_3436_);
lean_inc(v_u_3435_);
v___x_3473_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3435_, v_v_3436_, v_k_3437_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_dec_ref(v___x_3473_);
lean_inc_ref(v_k_3437_);
lean_inc_n(v_u_3435_, 2);
v___x_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3474_, 0, v_u_3435_);
lean_ctor_set(v___x_3474_, 1, v_k_3437_);
lean_ctor_set(v___x_3474_, 2, v_h_3438_);
lean_inc(v_v_3436_);
v___x_3475_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3435_, v_v_3436_, v___x_3474_, v___y_3452_, v___y_3453_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref(v___x_3475_);
lean_inc_ref(v_k_3437_);
lean_inc(v_v_3436_);
lean_inc(v_u_3435_);
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3435_, v_v_3436_, v_k_3437_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref(v___x_3476_);
v___x_3477_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3435_, v_v_3436_, v_k_3437_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref(v___x_3477_);
v___x_3478_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_);
return v___x_3478_;
}
else
{
return v___x_3477_;
}
}
else
{
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
return v___x_3476_;
}
}
else
{
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
return v___x_3475_;
}
}
else
{
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v_a_3480_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3463_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3463_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
v___jp_3488_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_3436_, v_u_3435_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref(v___x_3500_);
if (lean_obj_tag(v_a_3501_) == 1)
{
lean_object* v_val_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; 
v_val_3502_ = lean_ctor_get(v_a_3501_, 0);
lean_inc_n(v_val_3502_, 2);
lean_dec_ref(v_a_3501_);
v___x_3503_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3437_, v_val_3502_);
v___x_3504_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3503_);
lean_dec_ref(v___x_3503_);
if (v___x_3504_ == 0)
{
lean_dec(v_val_3502_);
v___y_3452_ = v___y_3489_;
v___y_3453_ = v___y_3490_;
v___y_3454_ = v___y_3491_;
v___y_3455_ = v___y_3492_;
v___y_3456_ = v___y_3493_;
v___y_3457_ = v___y_3494_;
v___y_3458_ = v___y_3495_;
v___y_3459_ = v___y_3496_;
v___y_3460_ = v___y_3497_;
v___y_3461_ = v___y_3498_;
v___y_3462_ = v___y_3499_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3435_, v_v_3436_, v_k_3437_, v_h_3438_, v_val_3502_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v_val_3502_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3513_; 
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3513_ == 0)
{
lean_object* v_unused_3514_; 
v_unused_3514_ = lean_ctor_get(v___x_3505_, 0);
lean_dec(v_unused_3514_);
v___x_3507_ = v___x_3505_;
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
else
{
lean_dec(v___x_3505_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3513_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v___x_3511_; 
v___x_3509_ = lean_box(0);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3509_);
v___x_3511_ = v___x_3507_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
else
{
return v___x_3505_;
}
}
}
else
{
lean_dec(v_a_3501_);
v___y_3452_ = v___y_3489_;
v___y_3453_ = v___y_3490_;
v___y_3454_ = v___y_3491_;
v___y_3455_ = v___y_3492_;
v___y_3456_ = v___y_3493_;
v___y_3457_ = v___y_3494_;
v___y_3458_ = v___y_3495_;
v___y_3459_ = v___y_3496_;
v___y_3460_ = v___y_3497_;
v___y_3461_ = v___y_3498_;
v___y_3462_ = v___y_3499_;
goto v___jp_3451_;
}
}
else
{
lean_object* v_a_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3522_; 
lean_dec_ref(v_h_3438_);
lean_dec_ref(v_k_3437_);
lean_dec(v_v_3436_);
lean_dec(v_u_3435_);
v_a_3515_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3517_ = v___x_3500_;
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_a_3515_);
lean_dec(v___x_3500_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3522_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3520_; 
if (v_isShared_3518_ == 0)
{
v___x_3520_ = v___x_3517_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_a_3515_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
}
v___jp_3523_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_box(0);
v___x_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
return v___x_3525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3612_, lean_object* v_v_3613_, lean_object* v_k_3614_, lean_object* v_h_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3612_, v_v_3613_, v_k_3614_, v_h_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec(v_a_3624_);
lean_dec_ref(v_a_3623_);
lean_dec(v_a_3622_);
lean_dec_ref(v_a_3621_);
lean_dec(v_a_3620_);
lean_dec_ref(v_a_3619_);
lean_dec(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec(v_a_3616_);
return v_res_3628_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3635_ = lean_box(0);
v___x_3636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3637_ = l_Lean_mkConst(v___x_3636_, v___x_3635_);
return v___x_3637_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v_cls_3643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3645_ = l_Lean_Name_append(v___x_3644_, v_cls_3643_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3646_, lean_object* v_e_3647_, lean_object* v_he_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; uint8_t v___y_3677_; lean_object* v_h_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v_options_3721_; uint8_t v_hasTrace_3722_; 
v_options_3721_ = lean_ctor_get(v_a_3658_, 2);
v_hasTrace_3722_ = lean_ctor_get_uint8(v_options_3721_, sizeof(void*)*1);
if (v_hasTrace_3722_ == 0)
{
v___y_3703_ = v_a_3649_;
v___y_3704_ = v_a_3650_;
v___y_3705_ = v_a_3651_;
v___y_3706_ = v_a_3652_;
v___y_3707_ = v_a_3653_;
v___y_3708_ = v_a_3654_;
v___y_3709_ = v_a_3655_;
v___y_3710_ = v_a_3656_;
v___y_3711_ = v_a_3657_;
v___y_3712_ = v_a_3658_;
v___y_3713_ = v_a_3659_;
goto v___jp_3702_;
}
else
{
lean_object* v_inheritedTraceOptions_3723_; lean_object* v_cls_3724_; lean_object* v___x_3725_; uint8_t v___x_3726_; 
v_inheritedTraceOptions_3723_ = lean_ctor_get(v_a_3658_, 13);
v_cls_3724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3726_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3723_, v_options_3721_, v___x_3725_);
if (v___x_3726_ == 0)
{
v___y_3703_ = v_a_3649_;
v___y_3704_ = v_a_3650_;
v___y_3705_ = v_a_3651_;
v___y_3706_ = v_a_3652_;
v___y_3707_ = v_a_3653_;
v___y_3708_ = v_a_3654_;
v___y_3709_ = v_a_3655_;
v___y_3710_ = v_a_3656_;
v___y_3711_ = v_a_3657_;
v___y_3712_ = v_a_3658_;
v___y_3713_ = v_a_3659_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3646_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref(v___x_3727_);
v___x_3729_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3724_, v_a_3728_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_dec_ref(v___x_3729_);
v___y_3703_ = v_a_3649_;
v___y_3704_ = v_a_3650_;
v___y_3705_ = v_a_3651_;
v___y_3706_ = v_a_3652_;
v___y_3707_ = v_a_3653_;
v___y_3708_ = v_a_3654_;
v___y_3709_ = v_a_3655_;
v___y_3710_ = v_a_3656_;
v___y_3711_ = v_a_3657_;
v___y_3712_ = v_a_3658_;
v___y_3713_ = v_a_3659_;
goto v___jp_3702_;
}
else
{
lean_dec_ref(v_he_3648_);
lean_dec_ref(v_e_3647_);
lean_dec_ref(v_c_3646_);
return v___x_3729_;
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v_he_3648_);
lean_dec_ref(v_e_3647_);
lean_dec_ref(v_c_3646_);
v_a_3730_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3727_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3727_);
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
v___jp_3661_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3678_, 0, v___y_3672_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*1, v___y_3677_);
v___x_3679_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3671_, v___y_3663_, v___x_3678_, v___y_3669_, v___y_3664_, v___y_3662_, v___y_3670_, v___y_3665_, v___y_3675_, v___y_3674_, v___y_3668_, v___y_3673_, v___y_3666_, v___y_3667_, v___y_3676_);
return v___x_3679_;
}
v___jp_3680_:
{
uint8_t v_kind_3693_; 
v_kind_3693_ = lean_ctor_get_uint8(v_c_3646_, sizeof(void*)*5);
if (v_kind_3693_ == 1)
{
lean_object* v_u_3694_; lean_object* v_v_3695_; lean_object* v_k_3696_; uint8_t v___x_3697_; 
v_u_3694_ = lean_ctor_get(v_c_3646_, 0);
lean_inc(v_u_3694_);
v_v_3695_ = lean_ctor_get(v_c_3646_, 1);
lean_inc(v_v_3695_);
v_k_3696_ = lean_ctor_get(v_c_3646_, 2);
lean_inc(v_k_3696_);
lean_dec_ref(v_c_3646_);
v___x_3697_ = 1;
v___y_3662_ = v___y_3683_;
v___y_3663_ = v_v_3695_;
v___y_3664_ = v___y_3682_;
v___y_3665_ = v___y_3685_;
v___y_3666_ = v___y_3690_;
v___y_3667_ = v___y_3691_;
v___y_3668_ = v___y_3688_;
v___y_3669_ = v_h_3681_;
v___y_3670_ = v___y_3684_;
v___y_3671_ = v_u_3694_;
v___y_3672_ = v_k_3696_;
v___y_3673_ = v___y_3689_;
v___y_3674_ = v___y_3687_;
v___y_3675_ = v___y_3686_;
v___y_3676_ = v___y_3692_;
v___y_3677_ = v___x_3697_;
goto v___jp_3661_;
}
else
{
lean_object* v_u_3698_; lean_object* v_v_3699_; lean_object* v_k_3700_; uint8_t v___x_3701_; 
v_u_3698_ = lean_ctor_get(v_c_3646_, 0);
lean_inc(v_u_3698_);
v_v_3699_ = lean_ctor_get(v_c_3646_, 1);
lean_inc(v_v_3699_);
v_k_3700_ = lean_ctor_get(v_c_3646_, 2);
lean_inc(v_k_3700_);
lean_dec_ref(v_c_3646_);
v___x_3701_ = 0;
v___y_3662_ = v___y_3683_;
v___y_3663_ = v_v_3699_;
v___y_3664_ = v___y_3682_;
v___y_3665_ = v___y_3685_;
v___y_3666_ = v___y_3690_;
v___y_3667_ = v___y_3691_;
v___y_3668_ = v___y_3688_;
v___y_3669_ = v_h_3681_;
v___y_3670_ = v___y_3684_;
v___y_3671_ = v_u_3698_;
v___y_3672_ = v_k_3700_;
v___y_3673_ = v___y_3689_;
v___y_3674_ = v___y_3687_;
v___y_3675_ = v___y_3686_;
v___y_3676_ = v___y_3692_;
v___y_3677_ = v___x_3701_;
goto v___jp_3661_;
}
}
v___jp_3702_:
{
lean_object* v_h_x3f_3714_; 
v_h_x3f_3714_ = lean_ctor_get(v_c_3646_, 4);
if (lean_obj_tag(v_h_x3f_3714_) == 1)
{
lean_object* v_e_3715_; lean_object* v_val_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_e_3715_ = lean_ctor_get(v_c_3646_, 3);
v_val_3716_ = lean_ctor_get(v_h_x3f_3714_, 0);
v___x_3717_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3647_);
v___x_3718_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3647_, v_he_3648_);
lean_inc(v_val_3716_);
lean_inc_ref(v_e_3715_);
v___x_3719_ = l_Lean_mkApp4(v___x_3717_, v_e_3647_, v_e_3715_, v_val_3716_, v___x_3718_);
v_h_3681_ = v___x_3719_;
v___y_3682_ = v___y_3703_;
v___y_3683_ = v___y_3704_;
v___y_3684_ = v___y_3705_;
v___y_3685_ = v___y_3706_;
v___y_3686_ = v___y_3707_;
v___y_3687_ = v___y_3708_;
v___y_3688_ = v___y_3709_;
v___y_3689_ = v___y_3710_;
v___y_3690_ = v___y_3711_;
v___y_3691_ = v___y_3712_;
v___y_3692_ = v___y_3713_;
goto v___jp_3680_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3647_, v_he_3648_);
v_h_3681_ = v___x_3720_;
v___y_3682_ = v___y_3703_;
v___y_3683_ = v___y_3704_;
v___y_3684_ = v___y_3705_;
v___y_3685_ = v___y_3706_;
v___y_3686_ = v___y_3707_;
v___y_3687_ = v___y_3708_;
v___y_3688_ = v___y_3709_;
v___y_3689_ = v___y_3710_;
v___y_3690_ = v___y_3711_;
v___y_3691_ = v___y_3712_;
v___y_3692_ = v___y_3713_;
goto v___jp_3680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3738_, lean_object* v_e_3739_, lean_object* v_he_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3738_, v_e_3739_, v_he_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec(v_a_3741_);
return v_res_3753_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3760_ = lean_box(0);
v___x_3761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3762_ = l_Lean_mkConst(v___x_3761_, v___x_3760_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_unsigned_to_nat(1u);
v___x_3764_ = lean_nat_to_int(v___x_3763_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = lean_nat_to_int(v___x_3765_);
return v___x_3766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_unsigned_to_nat(0u);
v___x_3773_ = l_Lean_Level_ofNat(v___x_3772_);
return v___x_3773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3774_ = lean_box(0);
v___x_3775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
lean_ctor_set(v___x_3776_, 1, v___x_3774_);
return v___x_3776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3779_ = l_Lean_Expr_const___override(v___x_3778_, v___x_3777_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3783_ = lean_box(0);
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3785_ = l_Lean_Expr_const___override(v___x_3784_, v___x_3783_);
return v___x_3785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_box(0);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3792_ = l_Lean_Expr_const___override(v___x_3791_, v___x_3790_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_box(0);
v___x_3830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3831_ = l_Lean_mkConst(v___x_3830_, v___x_3829_);
return v___x_3831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3835_, lean_object* v_e_3836_, lean_object* v_he_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v_k_x27_3853_; lean_object* v_h_3854_; uint8_t v_strict_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; uint8_t v___y_3911_; lean_object* v___x_3957_; 
v___x_3957_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4279_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_3960_ = v___x_3957_;
v_isShared_3961_ = v_isSharedCheck_4279_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3957_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4279_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; uint8_t v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; uint8_t v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v_h_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___x_4255_; 
v___x_4255_ = lean_unbox(v_a_3958_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; lean_object* v___x_4258_; 
lean_dec(v_a_3958_);
lean_dec_ref(v_he_3837_);
lean_dec_ref(v_e_3836_);
lean_dec_ref(v_c_3835_);
v___x_4256_ = lean_box(0);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_4256_);
v___x_4258_ = v___x_3960_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
else
{
lean_object* v_options_4260_; uint8_t v_hasTrace_4261_; 
lean_del_object(v___x_3960_);
v_options_4260_ = lean_ctor_get(v_a_3847_, 2);
v_hasTrace_4261_ = lean_ctor_get_uint8(v_options_4260_, sizeof(void*)*1);
if (v_hasTrace_4261_ == 0)
{
v___y_4237_ = v_a_3838_;
v___y_4238_ = v_a_3839_;
v___y_4239_ = v_a_3840_;
v___y_4240_ = v_a_3841_;
v___y_4241_ = v_a_3842_;
v___y_4242_ = v_a_3843_;
v___y_4243_ = v_a_3844_;
v___y_4244_ = v_a_3845_;
v___y_4245_ = v_a_3846_;
v___y_4246_ = v_a_3847_;
v___y_4247_ = v_a_3848_;
goto v___jp_4236_;
}
else
{
lean_object* v_inheritedTraceOptions_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_inheritedTraceOptions_4262_ = lean_ctor_get(v_a_3847_, 13);
v___x_4263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4262_, v_options_4260_, v___x_4264_);
if (v___x_4265_ == 0)
{
v___y_4237_ = v_a_3838_;
v___y_4238_ = v_a_3839_;
v___y_4239_ = v_a_3840_;
v___y_4240_ = v_a_3841_;
v___y_4241_ = v_a_3842_;
v___y_4242_ = v_a_3843_;
v___y_4243_ = v_a_3844_;
v___y_4244_ = v_a_3845_;
v___y_4245_ = v_a_3846_;
v___y_4246_ = v_a_3847_;
v___y_4247_ = v_a_3848_;
goto v___jp_4236_;
}
else
{
lean_object* v___x_4266_; 
v___x_4266_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3835_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref(v___x_4266_);
v___x_4268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4268_);
lean_ctor_set(v___x_4269_, 1, v_a_4267_);
v___x_4270_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4263_, v___x_4269_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_dec_ref(v___x_4270_);
v___y_4237_ = v_a_3838_;
v___y_4238_ = v_a_3839_;
v___y_4239_ = v_a_3840_;
v___y_4240_ = v_a_3841_;
v___y_4241_ = v_a_3842_;
v___y_4242_ = v_a_3843_;
v___y_4243_ = v_a_3844_;
v___y_4244_ = v_a_3845_;
v___y_4245_ = v_a_3846_;
v___y_4246_ = v_a_3847_;
v___y_4247_ = v_a_3848_;
goto v___jp_4236_;
}
else
{
lean_dec(v_a_3958_);
lean_dec_ref(v_he_3837_);
lean_dec_ref(v_e_3836_);
lean_dec_ref(v_c_3835_);
return v___x_4270_;
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_a_3958_);
lean_dec_ref(v_he_3837_);
lean_dec_ref(v_e_3836_);
lean_dec_ref(v_c_3835_);
v_a_4271_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4266_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4266_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
}
v___jp_3962_:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_3983_);
v___x_3985_ = l_Lean_mkApp6(v___y_3971_, v___y_3969_, v___y_3968_, v___y_3976_, v___y_3983_, v___x_3984_, v___y_3967_);
if (v___y_3973_ == 0)
{
uint8_t v___x_3986_; 
v___x_3986_ = lean_unbox(v_a_3958_);
lean_dec(v_a_3958_);
v___y_3894_ = v___y_3963_;
v___y_3895_ = v___y_3964_;
v___y_3896_ = v___y_3965_;
v___y_3897_ = v___y_3966_;
v___y_3898_ = v___x_3985_;
v___y_3899_ = v___y_3970_;
v___y_3900_ = v___y_3972_;
v___y_3901_ = v___y_3975_;
v___y_3902_ = v___y_3974_;
v___y_3903_ = v___y_3980_;
v___y_3904_ = v___y_3979_;
v___y_3905_ = v___y_3978_;
v___y_3906_ = v___y_3977_;
v___y_3907_ = v___x_3984_;
v___y_3908_ = v___y_3981_;
v___y_3909_ = v___y_3983_;
v___y_3910_ = v___y_3982_;
v___y_3911_ = v___x_3986_;
goto v___jp_3893_;
}
else
{
uint8_t v___x_3987_; 
lean_dec(v_a_3958_);
v___x_3987_ = 0;
v___y_3894_ = v___y_3963_;
v___y_3895_ = v___y_3964_;
v___y_3896_ = v___y_3965_;
v___y_3897_ = v___y_3966_;
v___y_3898_ = v___x_3985_;
v___y_3899_ = v___y_3970_;
v___y_3900_ = v___y_3972_;
v___y_3901_ = v___y_3975_;
v___y_3902_ = v___y_3974_;
v___y_3903_ = v___y_3980_;
v___y_3904_ = v___y_3979_;
v___y_3905_ = v___y_3978_;
v___y_3906_ = v___y_3977_;
v___y_3907_ = v___x_3984_;
v___y_3908_ = v___y_3981_;
v___y_3909_ = v___y_3983_;
v___y_3910_ = v___y_3982_;
v___y_3911_ = v___x_3987_;
goto v___jp_3893_;
}
}
v___jp_3988_:
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4010_ = lean_int_dec_le(v___x_4009_, v___y_3996_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4011_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4013_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4014_ = lean_int_neg(v___y_3996_);
v___x_4015_ = l_Int_toNat(v___x_4014_);
lean_dec(v___x_4014_);
v___x_4016_ = l_Lean_instToExprInt_mkNat(v___x_4015_);
v___x_4017_ = l_Lean_mkApp3(v___x_4011_, v___x_4012_, v___x_4013_, v___x_4016_);
v___y_3963_ = v___y_3989_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3991_;
v___y_3966_ = v___y_3992_;
v___y_3967_ = v___y_3993_;
v___y_3968_ = v___y_3994_;
v___y_3969_ = v___y_3995_;
v___y_3970_ = v___y_3996_;
v___y_3971_ = v___y_3997_;
v___y_3972_ = v___y_3998_;
v___y_3973_ = v___y_3999_;
v___y_3974_ = v___y_4001_;
v___y_3975_ = v___y_4000_;
v___y_3976_ = v___y_4008_;
v___y_3977_ = v___y_4005_;
v___y_3978_ = v___y_4004_;
v___y_3979_ = v___y_4003_;
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4006_;
v___y_3982_ = v___y_4007_;
v___y_3983_ = v___x_4017_;
goto v___jp_3962_;
}
else
{
lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4018_ = l_Int_toNat(v___y_3996_);
v___x_4019_ = l_Lean_instToExprInt_mkNat(v___x_4018_);
v___y_3963_ = v___y_3989_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3991_;
v___y_3966_ = v___y_3992_;
v___y_3967_ = v___y_3993_;
v___y_3968_ = v___y_3994_;
v___y_3969_ = v___y_3995_;
v___y_3970_ = v___y_3996_;
v___y_3971_ = v___y_3997_;
v___y_3972_ = v___y_3998_;
v___y_3973_ = v___y_3999_;
v___y_3974_ = v___y_4001_;
v___y_3975_ = v___y_4000_;
v___y_3976_ = v___y_4008_;
v___y_3977_ = v___y_4005_;
v___y_3978_ = v___y_4004_;
v___y_3979_ = v___y_4003_;
v___y_3980_ = v___y_4002_;
v___y_3981_ = v___y_4006_;
v___y_3982_ = v___y_4007_;
v___y_3983_ = v___x_4019_;
goto v___jp_3962_;
}
}
v___jp_4020_:
{
lean_object* v___x_4038_; 
lean_inc(v___y_4037_);
v___x_4038_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4037_, v___y_4036_, v___y_4035_, v___y_4031_, v___y_4032_, v___y_4021_, v___y_4029_, v___y_4033_, v___y_4027_, v___y_4025_, v___y_4030_, v___y_4034_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref(v___x_4038_);
v___x_4040_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4022_, v___y_4036_, v___y_4035_, v___y_4031_, v___y_4032_, v___y_4021_, v___y_4029_, v___y_4033_, v___y_4027_, v___y_4025_, v___y_4030_, v___y_4034_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v___x_4040_);
v___x_4042_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4023_, v___y_4036_, v___y_4035_, v___y_4031_, v___y_4032_, v___y_4021_, v___y_4029_, v___y_4033_, v___y_4027_, v___y_4025_, v___y_4030_, v___y_4034_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = lean_int_neg(v___y_4024_);
v___x_4045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4046_ = lean_int_dec_le(v___x_4045_, v___y_4024_);
if (v___x_4046_ == 0)
{
lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_dec(v___y_4024_);
v___x_4047_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4050_ = l_Int_toNat(v___x_4044_);
v___x_4051_ = l_Lean_instToExprInt_mkNat(v___x_4050_);
v___x_4052_ = l_Lean_mkApp3(v___x_4047_, v___x_4048_, v___x_4049_, v___x_4051_);
v___y_3989_ = v___y_4022_;
v___y_3990_ = v___y_4021_;
v___y_3991_ = v___y_4023_;
v___y_3992_ = v___y_4025_;
v___y_3993_ = v___y_4026_;
v___y_3994_ = v_a_4043_;
v___y_3995_ = v_a_4041_;
v___y_3996_ = v___x_4044_;
v___y_3997_ = v_a_4039_;
v___y_3998_ = v___y_4027_;
v___y_3999_ = v___y_4028_;
v___y_4000_ = v___y_4029_;
v___y_4001_ = v___y_4030_;
v___y_4002_ = v___y_4031_;
v___y_4003_ = v___y_4032_;
v___y_4004_ = v___y_4033_;
v___y_4005_ = v___y_4034_;
v___y_4006_ = v___y_4035_;
v___y_4007_ = v___y_4036_;
v___y_4008_ = v___x_4052_;
goto v___jp_3988_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4053_ = l_Int_toNat(v___y_4024_);
lean_dec(v___y_4024_);
v___x_4054_ = l_Lean_instToExprInt_mkNat(v___x_4053_);
v___y_3989_ = v___y_4022_;
v___y_3990_ = v___y_4021_;
v___y_3991_ = v___y_4023_;
v___y_3992_ = v___y_4025_;
v___y_3993_ = v___y_4026_;
v___y_3994_ = v_a_4043_;
v___y_3995_ = v_a_4041_;
v___y_3996_ = v___x_4044_;
v___y_3997_ = v_a_4039_;
v___y_3998_ = v___y_4027_;
v___y_3999_ = v___y_4028_;
v___y_4000_ = v___y_4029_;
v___y_4001_ = v___y_4030_;
v___y_4002_ = v___y_4031_;
v___y_4003_ = v___y_4032_;
v___y_4004_ = v___y_4033_;
v___y_4005_ = v___y_4034_;
v___y_4006_ = v___y_4035_;
v___y_4007_ = v___y_4036_;
v___y_4008_ = v___x_4054_;
goto v___jp_3988_;
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec(v_a_4041_);
lean_dec(v_a_4039_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v_a_3958_);
v_a_4055_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4042_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4042_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
else
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4070_; 
lean_dec(v_a_4039_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v_a_3958_);
v_a_4063_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4065_ = v___x_4040_;
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4040_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4070_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4068_; 
if (v_isShared_4066_ == 0)
{
v___x_4068_ = v___x_4065_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec(v___y_4022_);
lean_dec(v_a_3958_);
v_a_4071_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4038_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4038_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
v___jp_4079_:
{
lean_object* v___x_4092_; 
v___x_4092_ = l_Lean_Meta_Grind_Order_isRing(v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; uint8_t v___x_4094_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref(v___x_4092_);
v___x_4094_ = lean_unbox(v_a_4093_);
if (v___x_4094_ == 0)
{
uint8_t v_kind_4095_; 
v_kind_4095_ = lean_ctor_get_uint8(v_c_3835_, sizeof(void*)*5);
if (v_kind_4095_ == 1)
{
lean_object* v_u_4096_; lean_object* v_v_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec(v_a_3958_);
v_u_4096_ = lean_ctor_get(v_c_3835_, 0);
lean_inc(v_u_4096_);
v_v_4097_ = lean_ctor_get(v_c_3835_, 1);
lean_inc(v_v_4097_);
lean_dec_ref(v_c_3835_);
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4099_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4098_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4096_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref(v___x_4101_);
v___x_4103_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4097_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; uint8_t v___x_4108_; lean_object* v___x_4109_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
lean_inc(v_a_4104_);
lean_dec_ref(v___x_4103_);
v___x_4105_ = l_Lean_mkApp3(v_a_4100_, v_a_4102_, v_a_4104_, v_h_4080_);
v___x_4106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4107_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
v___x_4108_ = lean_unbox(v_a_4093_);
lean_dec(v_a_4093_);
lean_ctor_set_uint8(v___x_4107_, sizeof(void*)*1, v___x_4108_);
v___x_4109_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4097_, v_u_4096_, v___x_4107_, v___x_4105_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4109_;
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v_a_4102_);
lean_dec(v_a_4100_);
lean_dec(v_v_4097_);
lean_dec(v_u_4096_);
lean_dec(v_a_4093_);
lean_dec_ref(v_h_4080_);
v_a_4110_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4103_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4103_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_dec(v_a_4100_);
lean_dec(v_v_4097_);
lean_dec(v_u_4096_);
lean_dec(v_a_4093_);
lean_dec_ref(v_h_4080_);
v_a_4118_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4101_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4101_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_v_4097_);
lean_dec(v_u_4096_);
lean_dec(v_a_4093_);
lean_dec_ref(v_h_4080_);
v_a_4126_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4099_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4099_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
else
{
lean_object* v_u_4134_; lean_object* v_v_4135_; lean_object* v___x_4136_; 
lean_dec(v_a_4093_);
v_u_4134_ = lean_ctor_get(v_c_3835_, 0);
lean_inc(v_u_4134_);
v_v_4135_ = lean_ctor_get(v_c_3835_, 1);
lean_inc(v_v_4135_);
lean_dec_ref(v_c_3835_);
v___x_4136_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; uint8_t v___x_4138_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref(v___x_4136_);
v___x_4138_ = lean_unbox(v_a_4137_);
if (v___x_4138_ == 0)
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_dec(v_a_3958_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4140_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4139_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___x_4140_);
v___x_4142_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4134_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___x_4142_);
v___x_4144_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4135_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; lean_object* v___x_4150_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref(v___x_4144_);
v___x_4146_ = l_Lean_mkApp3(v_a_4141_, v_a_4143_, v_a_4145_, v_h_4080_);
v___x_4147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = lean_unbox(v_a_4137_);
lean_dec(v_a_4137_);
lean_ctor_set_uint8(v___x_4148_, sizeof(void*)*1, v___x_4149_);
v___x_4150_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4135_, v_u_4134_, v___x_4148_, v___x_4146_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4150_;
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec(v_a_4143_);
lean_dec(v_a_4141_);
lean_dec(v_a_4137_);
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
v_a_4151_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4144_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4144_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec(v_a_4141_);
lean_dec(v_a_4137_);
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
v_a_4159_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4142_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4142_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec(v_a_4137_);
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
v_a_4167_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4140_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4140_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
else
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
lean_dec(v_a_4137_);
v___x_4175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4176_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4175_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4134_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref(v___x_4178_);
v___x_4180_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4135_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; lean_object* v___x_4186_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_a_4181_);
lean_dec_ref(v___x_4180_);
v___x_4182_ = l_Lean_mkApp3(v_a_4177_, v_a_4179_, v_a_4181_, v_h_4080_);
v___x_4183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4184_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
v___x_4185_ = lean_unbox(v_a_3958_);
lean_dec(v_a_3958_);
lean_ctor_set_uint8(v___x_4184_, sizeof(void*)*1, v___x_4185_);
v___x_4186_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4135_, v_u_4134_, v___x_4184_, v___x_4182_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4186_;
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec(v_a_4179_);
lean_dec(v_a_4177_);
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
lean_dec(v_a_3958_);
v_a_4187_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4180_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4180_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
else
{
lean_object* v_a_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec(v_a_4177_);
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
lean_dec(v_a_3958_);
v_a_4195_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4178_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_a_4195_);
lean_dec(v___x_4178_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_a_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
lean_dec(v_a_3958_);
v_a_4203_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4205_ = v___x_4176_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4176_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
}
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_dec(v_v_4135_);
lean_dec(v_u_4134_);
lean_dec_ref(v_h_4080_);
lean_dec(v_a_3958_);
v_a_4211_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4136_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4136_);
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
}
else
{
uint8_t v_kind_4219_; 
lean_dec(v_a_4093_);
v_kind_4219_ = lean_ctor_get_uint8(v_c_3835_, sizeof(void*)*5);
if (v_kind_4219_ == 1)
{
lean_object* v_u_4220_; lean_object* v_v_4221_; lean_object* v_k_4222_; lean_object* v___x_4223_; 
v_u_4220_ = lean_ctor_get(v_c_3835_, 0);
lean_inc(v_u_4220_);
v_v_4221_ = lean_ctor_get(v_c_3835_, 1);
lean_inc(v_v_4221_);
v_k_4222_ = lean_ctor_get(v_c_3835_, 2);
lean_inc(v_k_4222_);
lean_dec_ref(v_c_3835_);
v___x_4223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4021_ = v___y_4085_;
v___y_4022_ = v_u_4220_;
v___y_4023_ = v_v_4221_;
v___y_4024_ = v_k_4222_;
v___y_4025_ = v___y_4089_;
v___y_4026_ = v_h_4080_;
v___y_4027_ = v___y_4088_;
v___y_4028_ = v_kind_4219_;
v___y_4029_ = v___y_4086_;
v___y_4030_ = v___y_4090_;
v___y_4031_ = v___y_4083_;
v___y_4032_ = v___y_4084_;
v___y_4033_ = v___y_4087_;
v___y_4034_ = v___y_4091_;
v___y_4035_ = v___y_4082_;
v___y_4036_ = v___y_4081_;
v___y_4037_ = v___x_4223_;
goto v___jp_4020_;
}
else
{
lean_object* v_u_4224_; lean_object* v_v_4225_; lean_object* v_k_4226_; lean_object* v___x_4227_; 
v_u_4224_ = lean_ctor_get(v_c_3835_, 0);
lean_inc(v_u_4224_);
v_v_4225_ = lean_ctor_get(v_c_3835_, 1);
lean_inc(v_v_4225_);
v_k_4226_ = lean_ctor_get(v_c_3835_, 2);
lean_inc(v_k_4226_);
lean_dec_ref(v_c_3835_);
v___x_4227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4021_ = v___y_4085_;
v___y_4022_ = v_u_4224_;
v___y_4023_ = v_v_4225_;
v___y_4024_ = v_k_4226_;
v___y_4025_ = v___y_4089_;
v___y_4026_ = v_h_4080_;
v___y_4027_ = v___y_4088_;
v___y_4028_ = v_kind_4219_;
v___y_4029_ = v___y_4086_;
v___y_4030_ = v___y_4090_;
v___y_4031_ = v___y_4083_;
v___y_4032_ = v___y_4084_;
v___y_4033_ = v___y_4087_;
v___y_4034_ = v___y_4091_;
v___y_4035_ = v___y_4082_;
v___y_4036_ = v___y_4081_;
v___y_4037_ = v___x_4227_;
goto v___jp_4020_;
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec_ref(v_h_4080_);
lean_dec(v_a_3958_);
lean_dec_ref(v_c_3835_);
v_a_4228_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4092_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4092_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
v___jp_4236_:
{
lean_object* v_h_x3f_4248_; 
v_h_x3f_4248_ = lean_ctor_get(v_c_3835_, 4);
if (lean_obj_tag(v_h_x3f_4248_) == 1)
{
lean_object* v_e_4249_; lean_object* v_val_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_e_4249_ = lean_ctor_get(v_c_3835_, 3);
v_val_4250_ = lean_ctor_get(v_h_x3f_4248_, 0);
v___x_4251_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3836_);
v___x_4252_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3836_, v_he_3837_);
lean_inc(v_val_4250_);
lean_inc_ref(v_e_4249_);
v___x_4253_ = l_Lean_mkApp4(v___x_4251_, v_e_3836_, v_e_4249_, v_val_4250_, v___x_4252_);
v_h_4080_ = v___x_4253_;
v___y_4081_ = v___y_4237_;
v___y_4082_ = v___y_4238_;
v___y_4083_ = v___y_4239_;
v___y_4084_ = v___y_4240_;
v___y_4085_ = v___y_4241_;
v___y_4086_ = v___y_4242_;
v___y_4087_ = v___y_4243_;
v___y_4088_ = v___y_4244_;
v___y_4089_ = v___y_4245_;
v___y_4090_ = v___y_4246_;
v___y_4091_ = v___y_4247_;
goto v___jp_4079_;
}
else
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3836_, v_he_3837_);
v_h_4080_ = v___x_4254_;
v___y_4081_ = v___y_4237_;
v___y_4082_ = v___y_4238_;
v___y_4083_ = v___y_4239_;
v___y_4084_ = v___y_4240_;
v___y_4085_ = v___y_4241_;
v___y_4086_ = v___y_4242_;
v___y_4087_ = v___y_4243_;
v___y_4088_ = v___y_4244_;
v___y_4089_ = v___y_4245_;
v___y_4090_ = v___y_4246_;
v___y_4091_ = v___y_4247_;
goto v___jp_4079_;
}
}
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v_he_3837_);
lean_dec_ref(v_e_3836_);
lean_dec_ref(v_c_3835_);
v_a_4280_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_3957_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_3957_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
v___jp_3850_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3867_, 0, v_k_x27_3853_);
lean_ctor_set_uint8(v___x_3867_, sizeof(void*)*1, v_strict_3855_);
v___x_3868_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3852_, v___y_3851_, v___x_3867_, v_h_3854_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
v___jp_3869_:
{
lean_object* v___x_3891_; uint8_t v___x_3892_; 
lean_inc_ref(v___y_3878_);
v___x_3891_ = l_Lean_mkApp6(v___y_3878_, v___y_3876_, v___y_3874_, v___y_3888_, v___y_3890_, v___y_3886_, v___y_3877_);
v___x_3892_ = 0;
v___y_3851_ = v___y_3870_;
v___y_3852_ = v___y_3873_;
v_k_x27_3853_ = v___y_3872_;
v_h_3854_ = v___x_3891_;
v_strict_3855_ = v___x_3892_;
v___y_3856_ = v___y_3889_;
v___y_3857_ = v___y_3887_;
v___y_3858_ = v___y_3884_;
v___y_3859_ = v___y_3885_;
v___y_3860_ = v___y_3871_;
v___y_3861_ = v___y_3881_;
v___y_3862_ = v___y_3883_;
v___y_3863_ = v___y_3879_;
v___y_3864_ = v___y_3875_;
v___y_3865_ = v___y_3880_;
v___y_3866_ = v___y_3882_;
goto v___jp_3850_;
}
v___jp_3893_:
{
lean_object* v___x_3912_; 
v___x_3912_ = l_Lean_Meta_Grind_Order_isInt(v___y_3910_, v___y_3908_, v___y_3903_, v___y_3904_, v___y_3895_, v___y_3901_, v___y_3905_, v___y_3900_, v___y_3897_, v___y_3902_, v___y_3906_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; uint8_t v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref(v___x_3912_);
v___x_3914_ = lean_unbox(v_a_3913_);
lean_dec(v_a_3913_);
if (v___x_3914_ == 0)
{
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3907_);
v___y_3851_ = v___y_3894_;
v___y_3852_ = v___y_3896_;
v_k_x27_3853_ = v___y_3899_;
v_h_3854_ = v___y_3898_;
v_strict_3855_ = v___y_3911_;
v___y_3856_ = v___y_3910_;
v___y_3857_ = v___y_3908_;
v___y_3858_ = v___y_3903_;
v___y_3859_ = v___y_3904_;
v___y_3860_ = v___y_3895_;
v___y_3861_ = v___y_3901_;
v___y_3862_ = v___y_3905_;
v___y_3863_ = v___y_3900_;
v___y_3864_ = v___y_3897_;
v___y_3865_ = v___y_3902_;
v___y_3866_ = v___y_3906_;
goto v___jp_3850_;
}
else
{
if (v___y_3911_ == 0)
{
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3907_);
v___y_3851_ = v___y_3894_;
v___y_3852_ = v___y_3896_;
v_k_x27_3853_ = v___y_3899_;
v_h_3854_ = v___y_3898_;
v_strict_3855_ = v___y_3911_;
v___y_3856_ = v___y_3910_;
v___y_3857_ = v___y_3908_;
v___y_3858_ = v___y_3903_;
v___y_3859_ = v___y_3904_;
v___y_3860_ = v___y_3895_;
v___y_3861_ = v___y_3901_;
v___y_3862_ = v___y_3905_;
v___y_3863_ = v___y_3900_;
v___y_3864_ = v___y_3897_;
v___y_3865_ = v___y_3902_;
v___y_3866_ = v___y_3906_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3915_; 
v___x_3915_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3896_, v___y_3910_, v___y_3908_, v___y_3903_, v___y_3904_, v___y_3895_, v___y_3901_, v___y_3905_, v___y_3900_, v___y_3897_, v___y_3902_, v___y_3906_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
v___x_3917_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3894_, v___y_3910_, v___y_3908_, v___y_3903_, v___y_3904_, v___y_3895_, v___y_3901_, v___y_3905_, v___y_3900_, v___y_3897_, v___y_3902_, v___y_3906_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref(v___x_3917_);
v___x_3919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3921_ = lean_int_sub(v___y_3899_, v___x_3920_);
lean_dec(v___y_3899_);
v___x_3922_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3923_ = lean_int_dec_le(v___x_3922_, v___x_3921_);
if (v___x_3923_ == 0)
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3927_ = lean_int_neg(v___x_3921_);
v___x_3928_ = l_Int_toNat(v___x_3927_);
lean_dec(v___x_3927_);
v___x_3929_ = l_Lean_instToExprInt_mkNat(v___x_3928_);
v___x_3930_ = l_Lean_mkApp3(v___x_3924_, v___x_3925_, v___x_3926_, v___x_3929_);
v___y_3870_ = v___y_3894_;
v___y_3871_ = v___y_3895_;
v___y_3872_ = v___x_3921_;
v___y_3873_ = v___y_3896_;
v___y_3874_ = v_a_3918_;
v___y_3875_ = v___y_3897_;
v___y_3876_ = v_a_3916_;
v___y_3877_ = v___y_3898_;
v___y_3878_ = v___x_3919_;
v___y_3879_ = v___y_3900_;
v___y_3880_ = v___y_3902_;
v___y_3881_ = v___y_3901_;
v___y_3882_ = v___y_3906_;
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___y_3903_;
v___y_3885_ = v___y_3904_;
v___y_3886_ = v___y_3907_;
v___y_3887_ = v___y_3908_;
v___y_3888_ = v___y_3909_;
v___y_3889_ = v___y_3910_;
v___y_3890_ = v___x_3930_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
v___x_3931_ = l_Int_toNat(v___x_3921_);
v___x_3932_ = l_Lean_instToExprInt_mkNat(v___x_3931_);
v___y_3870_ = v___y_3894_;
v___y_3871_ = v___y_3895_;
v___y_3872_ = v___x_3921_;
v___y_3873_ = v___y_3896_;
v___y_3874_ = v_a_3918_;
v___y_3875_ = v___y_3897_;
v___y_3876_ = v_a_3916_;
v___y_3877_ = v___y_3898_;
v___y_3878_ = v___x_3919_;
v___y_3879_ = v___y_3900_;
v___y_3880_ = v___y_3902_;
v___y_3881_ = v___y_3901_;
v___y_3882_ = v___y_3906_;
v___y_3883_ = v___y_3905_;
v___y_3884_ = v___y_3903_;
v___y_3885_ = v___y_3904_;
v___y_3886_ = v___y_3907_;
v___y_3887_ = v___y_3908_;
v___y_3888_ = v___y_3909_;
v___y_3889_ = v___y_3910_;
v___y_3890_ = v___x_3932_;
goto v___jp_3869_;
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec(v_a_3916_);
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3896_);
lean_dec(v___y_3894_);
v_a_3933_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3917_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3917_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3896_);
lean_dec(v___y_3894_);
v_a_3941_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3915_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3915_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref(v___y_3909_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3896_);
lean_dec(v___y_3894_);
v_a_3949_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3912_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3912_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4288_, lean_object* v_e_4289_, lean_object* v_he_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4288_, v_e_4289_, v_he_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec(v_a_4291_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4305_, v_a_4306_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4318_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4311_ = v___x_4308_;
v_isShared_4312_ = v_isSharedCheck_4318_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4308_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4318_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v_exprToStructId_4313_; lean_object* v___x_4314_; lean_object* v___x_4316_; 
v_exprToStructId_4313_ = lean_ctor_get(v_a_4309_, 2);
lean_inc_ref(v_exprToStructId_4313_);
lean_dec(v_a_4309_);
v___x_4314_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4313_, v_e_4304_);
lean_dec_ref(v_exprToStructId_4313_);
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 0, v___x_4314_);
v___x_4316_ = v___x_4311_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
v_a_4319_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4308_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4308_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4327_, v_a_4328_, v_a_4329_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_e_4327_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_){
_start:
{
lean_object* v___x_4344_; 
v___x_4344_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4332_, v_a_4333_, v_a_4341_);
return v___x_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
lean_dec(v_a_4355_);
lean_dec_ref(v_a_4354_);
lean_dec(v_a_4353_);
lean_dec_ref(v_a_4352_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec(v_a_4346_);
lean_dec_ref(v_e_4345_);
return v_res_4357_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = lean_box(0);
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4366_ = l_Lean_mkConst(v___x_4365_, v___x_4364_);
return v___x_4366_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = lean_box(0);
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4375_ = l_Lean_mkConst(v___x_4374_, v___x_4373_);
return v___x_4375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4376_, lean_object* v_e_x27_4377_, lean_object* v_he_x3f_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v___x_4390_; 
v___x_4390_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4377_, v_a_4379_, v_a_4387_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4481_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4481_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4481_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
if (lean_obj_tag(v_a_4391_) == 1)
{
lean_object* v_val_4395_; lean_object* v___x_4396_; 
lean_del_object(v___x_4393_);
v_val_4395_ = lean_ctor_get(v_a_4391_, 0);
lean_inc(v_val_4395_);
lean_dec_ref(v_a_4391_);
v___x_4396_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_x27_4377_, v_val_4395_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4468_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4399_ = v___x_4396_;
v_isShared_4400_ = v_isSharedCheck_4468_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4468_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
if (lean_obj_tag(v_a_4397_) == 1)
{
lean_object* v_val_4401_; lean_object* v___x_4402_; 
lean_del_object(v___x_4399_);
v_val_4401_ = lean_ctor_get(v_a_4397_, 0);
lean_inc(v_val_4401_);
lean_dec_ref(v_a_4397_);
lean_inc_ref(v_e_4376_);
v___x_4402_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4376_, v_a_4379_, v_a_4383_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; uint8_t v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref(v___x_4402_);
v___x_4404_ = lean_unbox(v_a_4403_);
lean_dec(v_a_4403_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; 
lean_inc_ref(v_e_4376_);
v___x_4405_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4376_, v_a_4379_, v_a_4383_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4431_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4408_ = v___x_4405_;
v_isShared_4409_ = v_isSharedCheck_4431_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___x_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4431_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
uint8_t v___x_4410_; 
v___x_4410_ = lean_unbox(v_a_4406_);
lean_dec(v_a_4406_);
if (v___x_4410_ == 0)
{
lean_object* v___x_4411_; lean_object* v___x_4413_; 
lean_dec(v_val_4401_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v___x_4411_ = lean_box(0);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4411_);
v___x_4413_ = v___x_4408_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4411_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
else
{
lean_object* v___x_4415_; 
lean_del_object(v___x_4408_);
lean_inc_ref(v_e_4376_);
v___x_4415_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4376_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4415_) == 0)
{
if (lean_obj_tag(v_he_x3f_4378_) == 1)
{
lean_object* v_a_4416_; lean_object* v_val_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref(v___x_4415_);
v_val_4417_ = lean_ctor_get(v_he_x3f_4378_, 0);
lean_inc(v_val_4417_);
lean_dec_ref(v_he_x3f_4378_);
v___x_4418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4377_);
v___x_4419_ = l_Lean_mkApp4(v___x_4418_, v_e_4376_, v_e_x27_4377_, v_val_4417_, v_a_4416_);
v___x_4420_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4401_, v_e_x27_4377_, v___x_4419_, v_val_4395_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_val_4395_);
return v___x_4420_;
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_4376_);
v_a_4421_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4421_);
lean_dec_ref(v___x_4415_);
v___x_4422_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4401_, v_e_x27_4377_, v_a_4421_, v_val_4395_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_val_4395_);
return v___x_4422_;
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_val_4401_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v_a_4423_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4415_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4415_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_val_4401_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v_a_4432_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4405_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4405_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
else
{
lean_object* v___x_4440_; 
lean_inc_ref(v_e_4376_);
v___x_4440_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4376_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4440_) == 0)
{
if (lean_obj_tag(v_he_x3f_4378_) == 1)
{
lean_object* v_a_4441_; lean_object* v_val_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref(v___x_4440_);
v_val_4442_ = lean_ctor_get(v_he_x3f_4378_, 0);
lean_inc(v_val_4442_);
lean_dec_ref(v_he_x3f_4378_);
v___x_4443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4377_);
v___x_4444_ = l_Lean_mkApp4(v___x_4443_, v_e_4376_, v_e_x27_4377_, v_val_4442_, v_a_4441_);
v___x_4445_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4401_, v_e_x27_4377_, v___x_4444_, v_val_4395_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_val_4395_);
return v___x_4445_;
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4447_; 
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_4376_);
v_a_4446_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4446_);
lean_dec_ref(v___x_4440_);
v___x_4447_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4401_, v_e_x27_4377_, v_a_4446_, v_val_4395_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_val_4395_);
return v___x_4447_;
}
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_val_4401_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
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
else
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4463_; 
lean_dec(v_val_4401_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v_a_4456_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4463_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4463_ == 0)
{
v___x_4458_ = v___x_4402_;
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v___x_4402_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4463_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4461_; 
if (v_isShared_4459_ == 0)
{
v___x_4461_ = v___x_4458_;
goto v_reusejp_4460_;
}
else
{
lean_object* v_reuseFailAlloc_4462_; 
v_reuseFailAlloc_4462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4456_);
v___x_4461_ = v_reuseFailAlloc_4462_;
goto v_reusejp_4460_;
}
v_reusejp_4460_:
{
return v___x_4461_;
}
}
}
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4466_; 
lean_dec(v_a_4397_);
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v___x_4464_ = lean_box(0);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___x_4464_);
v___x_4466_ = v___x_4399_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v___x_4464_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_val_4395_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v_a_4469_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4396_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4396_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
lean_dec(v_a_4391_);
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v___x_4477_ = lean_box(0);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4477_);
v___x_4479_ = v___x_4393_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
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
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4489_; 
lean_dec(v_he_x3f_4378_);
lean_dec_ref(v_e_x27_4377_);
lean_dec_ref(v_e_4376_);
v_a_4482_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4390_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4390_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4488_; 
v_reuseFailAlloc_4488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4488_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4488_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
return v___x_4487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4490_, lean_object* v_e_x27_4491_, lean_object* v_he_x3f_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4490_, v_e_x27_4491_, v_he_x3f_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
lean_dec(v_a_4500_);
lean_dec_ref(v_a_4499_);
lean_dec(v_a_4498_);
lean_dec_ref(v_a_4497_);
lean_dec(v_a_4496_);
lean_dec_ref(v_a_4495_);
lean_dec(v_a_4494_);
lean_dec(v_a_4493_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4506_, v_a_4514_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v_termMap_4519_; lean_object* v___x_4520_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref(v___x_4517_);
v_termMap_4519_ = lean_ctor_get(v_a_4518_, 3);
lean_inc_ref(v_termMap_4519_);
lean_dec(v_a_4518_);
v___x_4520_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4519_, v_e_4505_);
lean_dec_ref(v_termMap_4519_);
if (lean_obj_tag(v___x_4520_) == 1)
{
lean_object* v_val_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4531_; 
v_val_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4531_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4531_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4531_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_val_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4531_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_fst_4525_; lean_object* v_snd_4526_; lean_object* v___x_4528_; 
v_fst_4525_ = lean_ctor_get(v_val_4521_, 0);
lean_inc(v_fst_4525_);
v_snd_4526_ = lean_ctor_get(v_val_4521_, 1);
lean_inc(v_snd_4526_);
lean_dec(v_val_4521_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v_snd_4526_);
v___x_4528_ = v___x_4523_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4530_; 
v_reuseFailAlloc_4530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_snd_4526_);
v___x_4528_ = v_reuseFailAlloc_4530_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
lean_object* v___x_4529_; 
v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4505_, v_fst_4525_, v___x_4528_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
return v___x_4529_;
}
}
}
else
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
lean_dec(v___x_4520_);
v___x_4532_ = lean_box(0);
lean_inc_ref(v_e_4505_);
v___x_4533_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4505_, v_e_4505_, v___x_4532_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
return v___x_4533_;
}
}
else
{
lean_object* v_a_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4541_; 
lean_dec_ref(v_e_4505_);
v_a_4534_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4536_ = v___x_4517_;
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_a_4534_);
lean_dec(v___x_4517_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4541_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v___x_4539_; 
if (v_isShared_4537_ == 0)
{
v___x_4539_ = v___x_4536_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_a_4534_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
lean_dec(v_a_4552_);
lean_dec_ref(v_a_4551_);
lean_dec(v_a_4550_);
lean_dec_ref(v_a_4549_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec(v_a_4543_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_){
_start:
{
lean_object* v___x_4567_; 
v___x_4567_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
lean_dec(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec(v_a_4574_);
lean_dec_ref(v_a_4573_);
lean_dec(v_a_4572_);
lean_dec_ref(v_a_4571_);
lean_dec(v_a_4570_);
lean_dec(v_a_4569_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___f_4588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4590_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4589_, v___f_4588_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8____boxed(lean_object* v_a_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v___x_4605_; 
v___x_4605_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_);
return v___x_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
lean_dec(v_a_4616_);
lean_dec_ref(v_a_4615_);
lean_dec(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec(v_a_4612_);
lean_dec_ref(v_a_4611_);
lean_dec(v_a_4610_);
lean_dec_ref(v_a_4609_);
lean_dec(v_a_4608_);
lean_dec(v_a_4607_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___f_4625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_));
v___x_4627_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4626_, v___f_4625_);
return v___x_4627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8____boxed(lean_object* v_a_4628_){
_start:
{
lean_object* v_res_4629_; 
v_res_4629_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
return v_res_4629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
lean_object* v___x_4634_; 
v___x_4634_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4631_, v_a_4632_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4644_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4637_ = v___x_4634_;
v_isShared_4638_ = v_isSharedCheck_4644_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4634_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4644_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v_termMap_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v_termMap_4639_ = lean_ctor_get(v_a_4635_, 3);
lean_inc_ref(v_termMap_4639_);
lean_dec(v_a_4635_);
v___x_4640_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4639_, v_e_4630_);
lean_dec_ref(v_termMap_4639_);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 0, v___x_4640_);
v___x_4642_ = v___x_4637_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4640_);
v___x_4642_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
return v___x_4642_;
}
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
v_a_4645_ = lean_ctor_get(v___x_4634_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4634_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4634_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4634_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_){
_start:
{
lean_object* v_res_4657_; 
v_res_4657_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4653_, v_a_4654_, v_a_4655_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec_ref(v_e_4653_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4658_, v_a_4659_, v_a_4667_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_){
_start:
{
lean_object* v_res_4683_; 
v_res_4683_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_);
lean_dec(v_a_4681_);
lean_dec_ref(v_a_4680_);
lean_dec(v_a_4679_);
lean_dec_ref(v_a_4678_);
lean_dec(v_a_4677_);
lean_dec_ref(v_a_4676_);
lean_dec(v_a_4675_);
lean_dec_ref(v_a_4674_);
lean_dec(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_e_4671_);
return v_res_4683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4708_ = 0;
v___x_4709_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4710_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4710_, 0, v___x_4709_);
lean_ctor_set_uint8(v___x_4710_, sizeof(void*)*1, v___x_4708_);
return v___x_4710_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4713_ = l_Lean_stringToMessageData(v___x_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4714_, lean_object* v_b_4715_, lean_object* v_h_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_, lean_object* v_a_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v___y_4734_; lean_object* v___y_4735_; lean_object* v___y_4736_; lean_object* v___y_4737_; lean_object* v___y_4738_; lean_object* v___y_4739_; lean_object* v___x_4827_; 
v___x_4827_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4714_, v_a_4717_, v_a_4725_);
if (lean_obj_tag(v___x_4827_) == 0)
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4873_; 
v_a_4828_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4830_ = v___x_4827_;
v_isShared_4831_ = v_isSharedCheck_4873_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4827_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4873_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
if (lean_obj_tag(v_a_4828_) == 1)
{
lean_object* v_val_4832_; lean_object* v___x_4833_; 
lean_del_object(v___x_4830_);
v_val_4832_ = lean_ctor_get(v_a_4828_, 0);
lean_inc(v_val_4832_);
lean_dec_ref(v_a_4828_);
v___x_4833_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4715_, v_a_4717_, v_a_4725_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4860_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4860_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4860_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4860_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4860_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
if (lean_obj_tag(v_a_4834_) == 1)
{
lean_object* v_val_4838_; uint8_t v___x_4839_; 
v_val_4838_ = lean_ctor_get(v_a_4834_, 0);
lean_inc(v_val_4838_);
lean_dec_ref(v_a_4834_);
v___x_4839_ = lean_nat_dec_eq(v_val_4832_, v_val_4838_);
lean_dec(v_val_4838_);
if (v___x_4839_ == 0)
{
lean_object* v___x_4840_; lean_object* v___x_4842_; 
lean_dec(v_val_4832_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v___x_4840_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4840_);
v___x_4842_ = v___x_4836_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4840_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
else
{
lean_object* v_options_4844_; uint8_t v_hasTrace_4845_; 
lean_del_object(v___x_4836_);
v_options_4844_ = lean_ctor_get(v_a_4725_, 2);
v_hasTrace_4845_ = lean_ctor_get_uint8(v_options_4844_, sizeof(void*)*1);
if (v_hasTrace_4845_ == 0)
{
v___y_4729_ = v_val_4832_;
v___y_4730_ = v_a_4717_;
v___y_4731_ = v_a_4718_;
v___y_4732_ = v_a_4719_;
v___y_4733_ = v_a_4720_;
v___y_4734_ = v_a_4721_;
v___y_4735_ = v_a_4722_;
v___y_4736_ = v_a_4723_;
v___y_4737_ = v_a_4724_;
v___y_4738_ = v_a_4725_;
v___y_4739_ = v_a_4726_;
goto v___jp_4728_;
}
else
{
lean_object* v_inheritedTraceOptions_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; uint8_t v___x_4849_; 
v_inheritedTraceOptions_4846_ = lean_ctor_get(v_a_4725_, 13);
v___x_4847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4849_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4846_, v_options_4844_, v___x_4848_);
if (v___x_4849_ == 0)
{
v___y_4729_ = v_val_4832_;
v___y_4730_ = v_a_4717_;
v___y_4731_ = v_a_4718_;
v___y_4732_ = v_a_4719_;
v___y_4733_ = v_a_4720_;
v___y_4734_ = v_a_4721_;
v___y_4735_ = v_a_4722_;
v___y_4736_ = v_a_4723_;
v___y_4737_ = v_a_4724_;
v___y_4738_ = v_a_4725_;
v___y_4739_ = v_a_4726_;
goto v___jp_4728_;
}
else
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
lean_inc_ref(v_a_4714_);
v___x_4850_ = l_Lean_MessageData_ofExpr(v_a_4714_);
v___x_4851_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
lean_inc_ref(v_b_4715_);
v___x_4853_ = l_Lean_MessageData_ofExpr(v_b_4715_);
v___x_4854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4852_);
lean_ctor_set(v___x_4854_, 1, v___x_4853_);
v___x_4855_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4847_, v___x_4854_, v_a_4723_, v_a_4724_, v_a_4725_, v_a_4726_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_dec_ref(v___x_4855_);
v___y_4729_ = v_val_4832_;
v___y_4730_ = v_a_4717_;
v___y_4731_ = v_a_4718_;
v___y_4732_ = v_a_4719_;
v___y_4733_ = v_a_4720_;
v___y_4734_ = v_a_4721_;
v___y_4735_ = v_a_4722_;
v___y_4736_ = v_a_4723_;
v___y_4737_ = v_a_4724_;
v___y_4738_ = v_a_4725_;
v___y_4739_ = v_a_4726_;
goto v___jp_4728_;
}
else
{
lean_dec(v_val_4832_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
return v___x_4855_;
}
}
}
}
}
else
{
lean_object* v___x_4856_; lean_object* v___x_4858_; 
lean_dec(v_a_4834_);
lean_dec(v_val_4832_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v___x_4856_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4856_);
v___x_4858_ = v___x_4836_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
else
{
lean_object* v_a_4861_; lean_object* v___x_4863_; uint8_t v_isShared_4864_; uint8_t v_isSharedCheck_4868_; 
lean_dec(v_val_4832_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4861_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4868_ == 0)
{
v___x_4863_ = v___x_4833_;
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
else
{
lean_inc(v_a_4861_);
lean_dec(v___x_4833_);
v___x_4863_ = lean_box(0);
v_isShared_4864_ = v_isSharedCheck_4868_;
goto v_resetjp_4862_;
}
v_resetjp_4862_:
{
lean_object* v___x_4866_; 
if (v_isShared_4864_ == 0)
{
v___x_4866_ = v___x_4863_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
v___x_4866_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
return v___x_4866_;
}
}
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4871_; 
lean_dec(v_a_4828_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v___x_4869_ = lean_box(0);
if (v_isShared_4831_ == 0)
{
lean_ctor_set(v___x_4830_, 0, v___x_4869_);
v___x_4871_ = v___x_4830_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v___x_4869_);
v___x_4871_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
return v___x_4871_;
}
}
}
}
else
{
lean_object* v_a_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4874_ = lean_ctor_get(v___x_4827_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4827_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4827_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
v___jp_4728_:
{
lean_object* v___x_4740_; 
lean_inc_ref(v_a_4714_);
v___x_4740_ = l_Lean_Meta_Grind_Order_getNodeId(v_a_4714_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4742_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
lean_inc(v_a_4741_);
lean_dec_ref(v___x_4740_);
lean_inc_ref(v_b_4715_);
v___x_4742_ = l_Lean_Meta_Grind_Order_getNodeId(v_b_4715_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4742_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4744_; 
v_a_4743_ = lean_ctor_get(v___x_4742_, 0);
lean_inc(v_a_4743_);
lean_dec_ref(v___x_4742_);
v___x_4744_ = l_Lean_Meta_Grind_Order_isRing(v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v_a_4745_; uint8_t v___x_4746_; 
v_a_4745_ = lean_ctor_get(v___x_4744_, 0);
lean_inc(v_a_4745_);
lean_dec_ref(v___x_4744_);
v___x_4746_ = lean_unbox(v_a_4745_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4748_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4747_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc(v_a_4749_);
lean_dec_ref(v___x_4748_);
v___x_4750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4751_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4750_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref(v___x_4751_);
lean_inc_ref(v_h_4716_);
lean_inc_ref(v_b_4715_);
lean_inc_ref(v_a_4714_);
v___x_4753_ = l_Lean_mkApp3(v_a_4749_, v_a_4714_, v_b_4715_, v_h_4716_);
v___x_4754_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4755_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4755_, 0, v___x_4754_);
v___x_4756_ = lean_unbox(v_a_4745_);
lean_dec(v_a_4745_);
lean_ctor_set_uint8(v___x_4755_, sizeof(void*)*1, v___x_4756_);
lean_inc_ref(v___x_4755_);
lean_inc(v_a_4743_);
lean_inc(v_a_4741_);
v___x_4757_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4741_, v_a_4743_, v___x_4755_, v___x_4753_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v___x_4758_; lean_object* v___x_4759_; 
lean_dec_ref(v___x_4757_);
v___x_4758_ = l_Lean_mkApp3(v_a_4752_, v_a_4714_, v_b_4715_, v_h_4716_);
v___x_4759_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4743_, v_a_4741_, v___x_4755_, v___x_4758_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4729_);
return v___x_4759_;
}
else
{
lean_dec_ref(v___x_4755_);
lean_dec(v_a_4752_);
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
return v___x_4757_;
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v_a_4749_);
lean_dec(v_a_4745_);
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4760_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4751_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4751_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
else
{
lean_object* v_a_4768_; lean_object* v___x_4770_; uint8_t v_isShared_4771_; uint8_t v_isSharedCheck_4775_; 
lean_dec(v_a_4745_);
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4768_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4775_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4775_ == 0)
{
v___x_4770_ = v___x_4748_;
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
else
{
lean_inc(v_a_4768_);
lean_dec(v___x_4748_);
v___x_4770_ = lean_box(0);
v_isShared_4771_ = v_isSharedCheck_4775_;
goto v_resetjp_4769_;
}
v_resetjp_4769_:
{
lean_object* v___x_4773_; 
if (v_isShared_4771_ == 0)
{
v___x_4773_ = v___x_4770_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v_a_4768_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
else
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
lean_dec(v_a_4745_);
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4777_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4776_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
v___x_4779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4780_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4779_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc(v_a_4781_);
lean_dec_ref(v___x_4780_);
lean_inc_ref(v_h_4716_);
lean_inc_ref(v_b_4715_);
lean_inc_ref(v_a_4714_);
v___x_4782_ = l_Lean_mkApp3(v_a_4778_, v_a_4714_, v_b_4715_, v_h_4716_);
v___x_4783_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4743_);
lean_inc(v_a_4741_);
v___x_4784_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4741_, v_a_4743_, v___x_4783_, v___x_4782_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
lean_dec_ref(v___x_4784_);
v___x_4785_ = l_Lean_mkApp3(v_a_4781_, v_a_4714_, v_b_4715_, v_h_4716_);
v___x_4786_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4743_, v_a_4741_, v___x_4783_, v___x_4785_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
lean_dec(v___y_4729_);
return v___x_4786_;
}
else
{
lean_dec(v_a_4781_);
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
return v___x_4784_;
}
}
else
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4794_; 
lean_dec(v_a_4778_);
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4787_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4789_ = v___x_4780_;
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4780_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4794_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4792_; 
if (v_isShared_4790_ == 0)
{
v___x_4792_ = v___x_4789_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v_a_4787_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4795_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4777_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4777_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v_a_4743_);
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4803_ = lean_ctor_get(v___x_4744_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4744_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4744_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4744_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec(v_a_4741_);
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4811_ = lean_ctor_get(v___x_4742_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4742_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4742_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4742_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
lean_dec(v___y_4729_);
lean_dec_ref(v_h_4716_);
lean_dec_ref(v_b_4715_);
lean_dec_ref(v_a_4714_);
v_a_4819_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4740_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4740_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4882_, lean_object* v_b_4883_, lean_object* v_h_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4882_, v_b_4883_, v_h_4884_, v_a_4885_, v_a_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
lean_dec(v_a_4890_);
lean_dec_ref(v_a_4889_);
lean_dec(v_a_4888_);
lean_dec_ref(v_a_4887_);
lean_dec(v_a_4886_);
lean_dec(v_a_4885_);
return v_res_4896_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2(void){
_start:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4903_ = lean_box(0);
v___x_4904_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4905_ = l_Lean_mkConst(v___x_4904_, v___x_4903_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4906_, lean_object* v_b_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_){
_start:
{
uint8_t v___x_4919_; 
v___x_4919_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_4906_, v_b_4907_);
if (v___x_4919_ == 0)
{
lean_object* v___x_4920_; 
lean_inc(v_a_4917_);
lean_inc_ref(v_a_4916_);
lean_inc(v_a_4915_);
lean_inc_ref(v_a_4914_);
lean_inc(v_a_4913_);
lean_inc_ref(v_a_4912_);
lean_inc(v_a_4911_);
lean_inc_ref(v_a_4910_);
lean_inc(v_a_4909_);
lean_inc(v_a_4908_);
lean_inc_ref(v_b_4907_);
lean_inc_ref(v_a_4906_);
v___x_4920_ = lean_grind_mk_eq_proof(v_a_4906_, v_b_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
if (lean_obj_tag(v___x_4920_) == 0)
{
lean_object* v_a_4921_; lean_object* v___x_4922_; 
v_a_4921_ = lean_ctor_get(v___x_4920_, 0);
lean_inc(v_a_4921_);
lean_dec_ref(v___x_4920_);
v___x_4922_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4906_, v_a_4908_, v_a_4916_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
lean_inc(v_a_4923_);
lean_dec_ref(v___x_4922_);
if (lean_obj_tag(v_a_4923_) == 1)
{
lean_object* v_val_4924_; lean_object* v_fst_4925_; lean_object* v_snd_4926_; lean_object* v___x_4927_; 
v_val_4924_ = lean_ctor_get(v_a_4923_, 0);
lean_inc(v_val_4924_);
lean_dec_ref(v_a_4923_);
v_fst_4925_ = lean_ctor_get(v_val_4924_, 0);
lean_inc(v_fst_4925_);
v_snd_4926_ = lean_ctor_get(v_val_4924_, 1);
lean_inc(v_snd_4926_);
lean_dec(v_val_4924_);
v___x_4927_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4907_, v_a_4908_, v_a_4916_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4942_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4942_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4942_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
if (lean_obj_tag(v_a_4928_) == 1)
{
lean_object* v_val_4932_; lean_object* v_fst_4933_; lean_object* v_snd_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; 
lean_del_object(v___x_4930_);
v_val_4932_ = lean_ctor_get(v_a_4928_, 0);
lean_inc(v_val_4932_);
lean_dec_ref(v_a_4928_);
v_fst_4933_ = lean_ctor_get(v_val_4932_, 0);
lean_inc_n(v_fst_4933_, 2);
v_snd_4934_ = lean_ctor_get(v_val_4932_, 1);
lean_inc(v_snd_4934_);
lean_dec(v_val_4932_);
v___x_4935_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__2, &l_Lean_Meta_Grind_Order_processNewEq___closed__2_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2);
lean_inc(v_fst_4925_);
v___x_4936_ = l_Lean_mkApp7(v___x_4935_, v_a_4906_, v_b_4907_, v_fst_4925_, v_fst_4933_, v_snd_4926_, v_snd_4934_, v_a_4921_);
v___x_4937_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_fst_4925_, v_fst_4933_, v___x_4936_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4937_;
}
else
{
lean_object* v___x_4938_; lean_object* v___x_4940_; 
lean_dec(v_a_4928_);
lean_dec(v_snd_4926_);
lean_dec(v_fst_4925_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v___x_4938_ = lean_box(0);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4938_);
v___x_4940_ = v___x_4930_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
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
lean_dec(v_snd_4926_);
lean_dec(v_fst_4925_);
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4943_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4927_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4927_);
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
lean_object* v___x_4951_; 
lean_dec(v_a_4923_);
v___x_4951_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4906_, v_b_4907_, v_a_4921_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_);
return v___x_4951_;
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec(v_a_4921_);
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4952_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4922_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4922_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
else
{
lean_object* v_a_4960_; lean_object* v___x_4962_; uint8_t v_isShared_4963_; uint8_t v_isSharedCheck_4967_; 
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v_a_4960_ = lean_ctor_get(v___x_4920_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4920_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4920_);
v___x_4962_ = lean_box(0);
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
v_resetjp_4961_:
{
lean_object* v___x_4965_; 
if (v_isShared_4963_ == 0)
{
v___x_4965_ = v___x_4962_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
v___x_4965_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
return v___x_4965_;
}
}
}
}
else
{
lean_object* v___x_4968_; lean_object* v___x_4969_; 
lean_dec_ref(v_b_4907_);
lean_dec_ref(v_a_4906_);
v___x_4968_ = lean_box(0);
v___x_4969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4968_);
return v___x_4969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_4970_, lean_object* v_b_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_4970_, v_b_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
lean_dec(v_a_4979_);
lean_dec_ref(v_a_4978_);
lean_dec(v_a_4977_);
lean_dec_ref(v_a_4976_);
lean_dec(v_a_4975_);
lean_dec_ref(v_a_4974_);
lean_dec(v_a_4973_);
lean_dec(v_a_4972_);
return v_res_4983_;
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
